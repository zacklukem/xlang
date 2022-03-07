use std::collections::HashSet;

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
        let mut values = HashSet::with_capacity(self.constraints.len());
        for constraint in self.constraints.drain(..) {
            values.insert(constraint);
        }
        self.constraints = values.drain().collect();
    }

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
                            panic!("{}", ty);
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

    pub fn solve(&mut self) -> InferResult<HashMap<TyVarId, Ty<'ty>>> {
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

        self.clean_constraints();

        let mut cache = HashMap::new();
        let mut vars = HashMap::with_capacity(self.ty_vars.borrow().len());
        for var in self.ty_vars.borrow().iter() {
            let mut visited = HashSet::new();
            let val = self.solve_for(&self.constraints, &mut visited, &mut cache, *var);
            vars.insert(*var, val);
        }

        Ok(vars
            .into_iter()
            .filter(|(_, b)| b.is_some())
            .map(|(a, b)| (a, b.unwrap()))
            .collect())
    }
}

fn contains_ty_var<'ty>(id: TyVarId, ty: Ty<'ty>) -> bool {
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

pub fn unify<'ty>(
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
            // TODO: make this less... wrong
            if l_pt.is_integral() && r_pt.is_integral() {
                Ok(())
            } else if l_pt != r_pt {
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
