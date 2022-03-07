use super::*;

type VarCache<'ty> = HashMap<TyVarId, Ty<'ty>>;

impl<'mg, 'ty> InferCtx<'mg, 'ty> {
    // pub fn solve(&mut self) -> InferResult<()> {
    //     println!("B4: {:?}", self);
    // }

    fn clean_constraints(&mut self) {
        // self.constraints.dedup_by(|a, b| a.equiv(b));
        for constraint in self.constraints.iter_mut() {
            if let Constraint::Eq(lhs, Ty(Int(TyKind::TyVar(ty_var)))) = constraint {
                let lhs_prime = self.ctx.int(TyKind::TyVar(*ty_var));
                let rhs_prime = *lhs;
                *constraint = Constraint::Eq(lhs_prime, rhs_prime);
            }
        }
    }

    fn contains_id(&self, id: TyVarId, ty: Ty<'ty>) -> bool {
        match ty.0 .0 {
            TyKind::UnsizedArray(ty)
            | TyKind::Range(ty)
            | TyKind::SizedArray(_, ty)
            | TyKind::Pointer(_, ty) => self.contains_id(id, *ty),

            TyKind::Adt(AdtType { ty_params: tys, .. }) | TyKind::Tuple(tys) => {
                tys.iter().any(|ty| self.contains_id(id, *ty))
            }

            TyKind::Fun(tys, ty) => {
                tys.iter().any(|ty| self.contains_id(id, *ty)) || self.contains_id(id, *ty)
            }
            TyKind::TyVar(vid) => return *vid == id,
            TyKind::Primitive(_) | TyKind::Param(_) | TyKind::Err => false,
        }
    }

    fn solve_ty(&self, cache: &mut VarCache<'ty>, ty: Ty<'ty>) -> Option<Ty<'ty>> {
        let kind = match ty.0 .0 {
            TyKind::Pointer(pt, ty) => TyKind::Pointer(*pt, self.solve_ty(cache, *ty)?),
            TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.solve_ty(cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                TyKind::Tuple(tys)
            }
            TyKind::Fun(tys, ty) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.solve_ty(cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                let ty = self.solve_ty(cache, *ty)?;
                TyKind::Fun(tys, ty)
            }
            TyKind::SizedArray(size, ty) => TyKind::SizedArray(*size, self.solve_ty(cache, *ty)?),
            TyKind::UnsizedArray(ty) => TyKind::UnsizedArray(self.solve_ty(cache, *ty)?),
            TyKind::Range(ty) => TyKind::Range(self.solve_ty(cache, *ty)?),
            TyKind::Adt(AdtType {
                ty_params,
                path,
                def_id,
            }) => {
                let path = path.clone();
                let def_id = def_id.clone();
                let ty_params = ty_params
                    .iter()
                    .map(|ty| self.solve_ty(cache, *ty))
                    .collect::<Option<Vec<_>>>()?;
                TyKind::Adt(AdtType {
                    ty_params,
                    path,
                    def_id,
                })
            }
            TyKind::TyVar(id) => return self.solve_for(cache, *id),
            TyKind::Primitive(_) | TyKind::Param(_) | TyKind::Err => return Some(ty),
        };
        Some(self.ctx.int(kind))
    }

    fn solve_for(&self, cache: &mut VarCache<'ty>, id: TyVarId) -> Option<Ty<'ty>> {
        if let Some(ty) = cache.get(&id) {
            return Some(*ty);
        }
        for constraint in &self.constraints {
            match constraint {
                Constraint::Eq(ty, Ty(Int(TyKind::TyVar(var_id))))
                | Constraint::Eq(Ty(Int(TyKind::TyVar(var_id))), ty)
                    if *var_id == id =>
                {
                    if let Some(ty) = self.solve_ty(cache, *ty) {
                        cache.insert(id, ty);
                        return Some(ty);
                    }
                }
                Constraint::Field(ty, field, Ty(Int(TyKind::TyVar(var_id)))) if *var_id == id => {
                    if let Some(ty) = self.solve_ty(cache, *ty) {
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
            let val = self.solve_for(&mut cache, *var);
            vars.insert(*var, val);
        }
        for (id, ty) in vars.iter() {
            if let Some(ty) = ty {
                println!("SOLVED: ?{} := {}", id.to_human_readable(), *ty);
            } else {
                println!("UNSOLVED: ?{}", id.to_human_readable());
            }
        }
        Ok(vars.into_iter().map(|(a, b)| (a, b.unwrap())).collect())
    }
}
