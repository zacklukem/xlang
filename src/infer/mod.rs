use crate::ty::{AdtType, Ty, TyCtx, TyKind};
use std::cell::Cell;

#[derive(Debug)]
pub enum InferError {
    MismatchedTypes,
}
use InferError::*;

pub type InferResult<T> = Result<T, InferError>;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TyVarId(u32);

#[derive(Debug)]
pub enum Constraint<'ty> {
    Eq(Ty<'ty>, Ty<'ty>),
}

#[derive(Debug)]
pub struct InferCtx<'ty> {
    ctx: TyCtx<'ty>,
    next_id: Cell<u32>,
    constraints: Vec<Constraint<'ty>>,
}

impl<'ty> InferCtx<'ty> {
    pub fn new(ctx: TyCtx<'ty>) -> Self {
        InferCtx {
            ctx,
            next_id: Cell::new(0),
            constraints: Default::default(),
        }
    }

    fn mk_var_id(&self) -> TyVarId {
        let id = self.next_id.get();
        self.next_id.set(id + 1);
        TyVarId(id)
    }

    pub fn mk_var(&self) -> Ty<'ty> {
        self.ctx.int(TyKind::TyVar(self.mk_var_id()))
    }

    pub fn eq(&mut self, lhs: Ty<'ty>, rhs: Ty<'ty>) -> InferResult<()> {
        match (lhs.0 .0, rhs.0 .0) {
            (TyKind::Pointer(l_pt, l_inner), TyKind::Pointer(r_pt, r_inner)) => {
                if *l_pt != *r_pt {
                    Err(MismatchedTypes)
                } else {
                    self.eq(*l_inner, *r_inner)
                }
            }
            (TyKind::Tuple(l_tys), TyKind::Tuple(r_tys)) => {
                if l_tys.len() != r_tys.len() {
                    Err(MismatchedTypes)
                } else {
                    for (lhs, rhs) in l_tys.iter().zip(r_tys) {
                        self.eq(*lhs, *rhs)?;
                    }
                    Ok(())
                }
            }
            (TyKind::Fun(l_params, l_ret), TyKind::Fun(r_params, r_ret)) => {
                self.eq(*l_ret, *r_ret)?;
                if l_params.len() != r_params.len() {
                    Err(MismatchedTypes)
                } else {
                    for (lhs, rhs) in l_params.iter().zip(r_params) {
                        self.eq(*lhs, *rhs)?;
                    }
                    Ok(())
                }
            }
            (TyKind::SizedArray(l_size, l_inner), TyKind::SizedArray(r_size, r_inner)) => {
                if l_size != r_size {
                    Err(MismatchedTypes)
                } else {
                    self.eq(*l_inner, *r_inner)
                }
            }
            (TyKind::UnsizedArray(l_inner), TyKind::UnsizedArray(r_inner)) => {
                self.eq(*l_inner, *r_inner)
            }
            (TyKind::Range(l_inner), TyKind::Range(r_inner)) => self.eq(*l_inner, *r_inner),

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
                    Err(MismatchedTypes)
                } else {
                    for (lhs, rhs) in l_ty_params.iter().zip(r_ty_params) {
                        self.eq(*lhs, *rhs)?;
                    }
                    Ok(())
                }
            }

            // Other types such as TyVars, params and primitives can just be directly equated
            _ => {
                self.constraints.push(Constraint::Eq(lhs, rhs));
                Ok(())
            }
        }
    }
}
