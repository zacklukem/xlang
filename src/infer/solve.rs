//! Code for solving a [`InferCtx`]
//!
//! The algorithm is somewhat naive, but works ok for basic type inference.
//!
//! The basic algorithm is first to clean the constraints by moving any single
//! type variables to be the left operand of their respective equality predicates,
//! then removing any exact duplicate constraints.  This is done in the
//! [`clean_constraints`] function.
//!
//! Next the algorithm iterates over the constraints and tries to substitute and
//! unify type variables purely iterating downwards.  This part of the algorithm
//! is somewhat flawed and should be replaced or removed (the whole algorithm is
//! not very easy to prove or efficient)
//!
//! Next the algorithm iterates over all type variables and attempts to solve
//! for the type variables type.  This is done by calling the [`solve_for`]
//! function which recursively looks for a type variable and solves for any
//! unsolved type variables in the right side of a constraint.  This caches
//! all solved type variables for efficiency and maintains a list of all
//! visited type variables to prevent infinite recursion.  If there is no simple
//! constraint for a type variable, the algorithm attempts to unify the variable
//! and solve for it again.
//!
//! Next the algorithm looks at each [`Constraint::Method`] and attempts to unify
//! the constraint.
//!
//! Finally, the algorithm once again iterates through all type variables and
//! attempts to solve the remaining unsolved variables using [`solve_for`]

use std::collections::HashSet;

use log::debug;

use crate::ty::{self, PrimitiveType};

use super::*;

type VarCache<'ty> = HashMap<TyVarId, Ty<'ty>>;

impl<'mg, 'ty> InferCtx<'mg, 'ty> {
    fn clean_constraints(&mut self) {
        for constraint in self.constraints.iter_mut() {
            if let Constraint::Eq(lhs, Ty(Int(TyKind::TyVar(ty_var)))) = constraint {
                let lhs_prime = self.ctx.int(TyKind::TyVar(*ty_var));
                let rhs_prime = *lhs;
                *constraint = Constraint::Eq(lhs_prime, rhs_prime);
            }
        }
        // TODO: this randomizes the order of the constraints which may lead to
        //       inconsistent compilation results
        let mut values = HashSet::with_capacity(self.constraints.len());
        for constraint in self.constraints.drain(..) {
            values.insert(constraint);
        }
        self.constraints = values.drain().collect();
    }

    /// Solve a type that may contain type vars
    fn solve_ty(
        &self,
        constraints: &[Constraint<'ty>],
        visited: &mut HashSet<TyVarId>,
        cache: &mut VarCache<'ty>,
        ty: Ty<'ty>,
    ) -> Option<Ty<'ty>> {
        let kind = match ty.0 .0 {
            TyKind::Pointer(pt, ty) => {
                TyKind::Pointer(*pt, self.solve_ty(constraints, visited, cache, *ty)?)
            }
            TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.solve_ty(constraints, visited, cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                TyKind::Tuple(tys)
            }
            TyKind::Fun(tys, ty) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.solve_ty(constraints, visited, cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                let ty = self.solve_ty(constraints, visited, cache, *ty)?;
                TyKind::Fun(tys, ty)
            }
            TyKind::SizedArray(size, ty) => {
                TyKind::SizedArray(*size, self.solve_ty(constraints, visited, cache, *ty)?)
            }
            TyKind::UnsizedArray(ty) => {
                TyKind::UnsizedArray(self.solve_ty(constraints, visited, cache, *ty)?)
            }
            TyKind::Range(ty) => TyKind::Range(self.solve_ty(constraints, visited, cache, *ty)?),
            TyKind::Adt(AdtType {
                ty_params,
                path,
                def_id,
            }) => {
                let path = path.clone();
                let def_id = def_id.clone();
                let ty_params = ty_params
                    .iter()
                    .map(|ty| self.solve_ty(constraints, visited, cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                TyKind::Adt(AdtType {
                    ty_params,
                    path,
                    def_id,
                })
            }
            TyKind::TyVar(id) => return self.solve_for(constraints, visited, cache, *id),
            TyKind::Primitive(_) | TyKind::Param(_) | TyKind::Err => return Some(ty),
        };
        Some(self.ctx.int(kind))
    }

    /// Solve for a given type var with the given constraints
    fn solve_for(
        &self,
        constraints: &[Constraint<'ty>],
        visited: &mut HashSet<TyVarId>,
        cache: &mut VarCache<'ty>,
        id: TyVarId,
    ) -> Option<Ty<'ty>> {
        // Don't infinite loop
        if visited.contains(&id) {
            return None;
        }
        visited.insert(id);
        if let Some(ty) = cache.get(&id) {
            return Some(*ty);
        }
        for constraint in constraints {
            match constraint {
                Constraint::Eq(ty, Ty(Int(TyKind::TyVar(var_id))))
                | Constraint::Eq(Ty(Int(TyKind::TyVar(var_id))), ty)
                    if *var_id == id =>
                {
                    if let Some(ty) = self.solve_ty(constraints, visited, cache, *ty) {
                        cache.insert(id, ty);
                        return Some(ty);
                    }
                }
                Constraint::Field(ty, field, Ty(Int(TyKind::TyVar(var_id)))) if *var_id == id => {
                    if let Some(ty) = self.solve_ty(constraints, visited, cache, *ty) {
                        if let TyKind::Adt(adt) = ty.full_deref_ty().0 .0 {
                            let ty = adt.get_field(self.md, field).unwrap();
                            cache.insert(id, ty);
                            return Some(ty);
                        } else {
                            // panic!("{}", ty);
                        }
                    }
                }
                _ => (),
            }
        }
        for constraint in constraints {
            match constraint {
                Constraint::Eq(ty, Ty(Int(TyKind::TyVar(var_id))))
                | Constraint::Eq(Ty(Int(TyKind::TyVar(var_id))), ty)
                    if contains_ty_var(id, *ty) =>
                {
                    if let Some(other_ty) = self.solve_for(constraints, visited, cache, *var_id) {
                        let mut constraints = constraints.to_owned();
                        unify(&mut constraints, other_ty, *ty).unwrap();
                        for constraint in &constraints {
                            match constraint {
                                Constraint::Eq(ty, Ty(Int(TyKind::TyVar(var_id))))
                                | Constraint::Eq(Ty(Int(TyKind::TyVar(var_id))), ty)
                                    if *var_id == id =>
                                {
                                    if let Some(ty) =
                                        self.solve_ty(&constraints, visited, cache, *ty)
                                    {
                                        cache.insert(id, ty);
                                        return Some(ty);
                                    }
                                }
                                _ => (),
                            }
                        }
                        // if let Some(ty) = self.solve_for(&constraints, visited, cache, id) {
                        //     cache.insert(id, ty);
                        //     return Some(ty);
                        // }
                    }
                }
                _ => (),
            }
        }
        None
    }

    /// Solves the [`InferCtx`] for all type variables.
    ///
    /// Returns a map of type variables to definite types.
    ///
    /// See [`infer::solve`] for details.
    pub fn solve(&mut self) -> InferResult<SolveReplacements<'ty>> {
        self.clean_constraints();

        {
            let mut constraints = self.constraints.clone();
            while let Some(constraint) = constraints.pop() {
                match constraint {
                    Constraint::Eq(ty_var, ty) if matches!(ty_var, Ty(Int(TyKind::TyVar(_)))) => {
                        if is_definite_ty(ty) {
                            self.constraints.push(Constraint::Eq(ty_var, ty));
                        }
                        for constraint in &constraints {
                            match constraint {
                                Constraint::Eq(sub_ty_var, sub_ty) if ty_var == *sub_ty_var => {
                                    self.eq(ty, *sub_ty)?;
                                }
                                _ => (),
                            }
                        }
                    }
                    _ => (),
                }
            }
        }

        let mut cache = HashMap::new();
        let mut vars: HashMap<TyVarId, Option<Ty<'ty>>> =
            HashMap::with_capacity(self.ty_vars.borrow().len());

        // TODO: this is probably pretty slow...
        for _ in 0..20 {
            self.clean_constraints();

            for var in self.ty_vars.borrow().iter() {
                if !vars.contains_key(var) || vars[var].is_none() {
                    let mut visited = HashSet::new();
                    let val = self.solve_for(&self.constraints, &mut visited, &mut cache, *var);
                    vars.insert(*var, val);
                }
            }

            self.clean_constraints();

            // TODO: maybe dont copy the constraints..
            for constraint in self.constraints.clone().into_iter() {
                match constraint {
                    Constraint::Method(ty, method, target_ty) => {
                        let mut visited = HashSet::new();
                        let struct_ty =
                            self.solve_ty(&self.constraints, &mut visited, &mut cache, ty);
                        if let Some(Ty(Int(TyKind::Adt(adt)))) = struct_ty {
                            if let Some(method_ty) = adt.get_method_ty(self.md, &method) {
                                self.eq(method_ty, target_ty)?;
                            }
                        }
                    }
                    _ => (),
                }
            }

            for constraint in self.constraints.clone().into_iter() {
                if let Constraint::Integral(Ty(Int(TyKind::TyVar(ty_var)))) = constraint {
                    if vars.get(ty_var).unwrap().is_none() {
                        vars.insert(
                            *ty_var,
                            Some(ty::primitive_ty(self.ctx, PrimitiveType::I32)),
                        );
                        let ty_var = self.ctx.int(TyKind::TyVar(*ty_var));
                        self.eq(ty_var, ty::primitive_ty(self.ctx, PrimitiveType::I32))
                            .unwrap();
                    }
                }
            }

            if vars.values().all(|v| v.is_some()) {
                break;
            }
        }

        for (id, var) in &vars {
            if var.is_none() {
                return Err(UnableToResolve(*id));
            }
        }

        let out = SolveReplacements {
            ty_vars: vars
                .into_iter()
                .filter(|(_, b)| b.is_some())
                .map(|(a, b)| (a, b.unwrap()))
                .collect(),
        };

        debug!("ASDFASDF");
        debug!("Self {:#?}", self);
        debug!("Out {:#?}", out);

        Ok(out)
    }
}

/// Returns true if the given type contains the given type var
pub fn contains_ty_var<'ty>(id: TyVarId, ty: Ty<'ty>) -> bool {
    match ty.0 .0 {
        TyKind::Tuple(tys) | TyKind::Adt(AdtType { ty_params: tys, .. }) => {
            tys.iter().any(|ty| contains_ty_var(id, *ty))
        }

        TyKind::Pointer(_, ty)
        | TyKind::SizedArray(_, ty)
        | TyKind::UnsizedArray(ty)
        | TyKind::Range(ty) => contains_ty_var(id, *ty),

        TyKind::Fun(tys, ty) => {
            tys.iter().any(|ty| contains_ty_var(id, *ty)) || contains_ty_var(id, *ty)
        }

        TyKind::TyVar(var_id) => *var_id == id,
        TyKind::Primitive(_) | TyKind::Param(_) | TyKind::Err => false,
    }
}

/// Unify two types into the given list of constraints
fn unify<'ty>(
    constraints: &mut Vec<Constraint<'ty>>,
    lhs: Ty<'ty>,
    rhs: Ty<'ty>,
) -> InferResult<()> {
    let mismatch = || MismatchedTypes(format!("{} != {}", lhs, rhs));
    match (lhs.0 .0, rhs.0 .0) {
        (TyKind::Pointer(l_pt, l_inner), TyKind::Pointer(r_pt, r_inner)) => {
            if *l_pt != *r_pt {
                Err(mismatch())
            } else {
                unify(constraints, *l_inner, *r_inner)
            }
        }
        (TyKind::Tuple(l_tys), TyKind::Tuple(r_tys)) => {
            if l_tys.len() != r_tys.len() {
                Err(mismatch())
            } else {
                for (lhs, rhs) in l_tys.iter().zip(r_tys) {
                    unify(constraints, *lhs, *rhs)?;
                }
                Ok(())
            }
        }
        (TyKind::Fun(l_params, l_ret), TyKind::Fun(r_params, r_ret)) => {
            unify(constraints, *l_ret, *r_ret)?;
            if l_params.len() != r_params.len() {
                Err(mismatch())
            } else {
                for (lhs, rhs) in l_params.iter().zip(r_params) {
                    unify(constraints, *lhs, *rhs)?;
                }
                Ok(())
            }
        }
        (TyKind::SizedArray(l_size, l_inner), TyKind::SizedArray(r_size, r_inner)) => {
            if l_size != r_size {
                Err(mismatch())
            } else {
                unify(constraints, *l_inner, *r_inner)
            }
        }
        (TyKind::UnsizedArray(l_inner), TyKind::UnsizedArray(r_inner)) => {
            unify(constraints, *l_inner, *r_inner)
        }
        (TyKind::Range(l_inner), TyKind::Range(r_inner)) => unify(constraints, *l_inner, *r_inner),

        // Adt
        (
            TyKind::Adt(AdtType {
                def_id: l_def_id,
                ty_params: l_ty_params,
                ..
            }),
            TyKind::Adt(AdtType {
                def_id: r_def_id,
                ty_params: r_ty_params,
                ..
            }),
        ) => {
            if l_def_id != r_def_id || l_ty_params.len() != r_ty_params.len() {
                Err(mismatch())
            } else {
                for (lhs, rhs) in l_ty_params.iter().zip(r_ty_params) {
                    unify(constraints, *lhs, *rhs)?;
                }
                Ok(())
            }
        }
        (TyKind::Param(l_name), TyKind::Param(r_name)) => {
            if l_name != r_name {
                Err(mismatch())
            } else {
                Ok(())
            }
        }
        (TyKind::Primitive(l_pt), TyKind::Primitive(r_pt)) => {
            if l_pt != r_pt {
                Err(mismatch())
            } else {
                Ok(())
            }
        }
        // Other types such as TyVars be directly equated
        _ => {
            constraints.push(Constraint::Eq(lhs, rhs));
            Ok(())
        }
    }
}
