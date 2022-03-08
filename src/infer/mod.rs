pub mod solve;

use crate::ast::Span;
use crate::error_context::ErrorContext;
use crate::intern::Int;
use crate::ir;
use crate::tir::tir_infer::replace_ty_int;
use crate::ty::{AdtType, Ty, TyCtx, TyKind};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use InferError::*;

#[derive(Debug)]
pub enum InferError {
    MismatchedTypes(String),
    ExpectedAdt(String),
    UnableToResolve(TyVarId),
}

pub type InferResult<T> = Result<T, InferError>;

pub trait EmitResult {
    fn emit(self, err: &mut ErrorContext, span: &Span) -> Self;
}

impl<T> EmitResult for InferResult<T> {
    fn emit(self, err: &mut ErrorContext, span: &Span) -> Self {
        if let Err(MismatchedTypes(s)) = &self {
            err.err(format!("Mismatched types: {s}"), span);
            self
        } else if let Err(_) = &self {
            self.unwrap();
            unreachable!();
        } else {
            self
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TyVarId(u32);

impl TyVarId {
    pub fn to_human_readable(self) -> String {
        let mut id = self.0 + 1;
        let mut out = String::new();
        while id != 0 {
            let ch = char::from_u32((id % 26) + (b'A' as u32)).unwrap();
            out.push(ch);
            id /= 26;
        }
        out
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constraint<'ty> {
    /// `{0}` equals `{1}`
    Eq(Ty<'ty>, Ty<'ty>),
    /// `{0}` has field named `{1}` with type `{2}`
    Field(Ty<'ty>, String, Ty<'ty>),
    /// `{0}` has method named `{1}` with type `{2}`
    ///
    /// Example of use:
    /// ```xlang
    /// let value = something();
    /// let out: SomeType = value.method(arg1, arg2);
    /// -- Method(value_ty, "method", Fun([arg1_ty, arg2_ty], out_ty))
    /// ```
    Method(Ty<'ty>, String, Ty<'ty>),
}

impl<'ty> Constraint<'ty> {
    pub fn equiv(&self, rhs: &Constraint<'ty>) -> bool {
        match (self, rhs) {
            (Constraint::Eq(ty0l, ty1l), Constraint::Eq(ty0r, ty1r)) => {
                ty0l == ty0r && ty1l == ty1r || ty0l == ty1r && ty1l == ty0r
            }
            _ => self == rhs,
        }
    }
}

impl<'ty> Display for Constraint<'ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Constraint::Eq(lhs, rhs) => write!(f, "{lhs} === {rhs}"),
            Constraint::Field(lhs, field, rhs) => write!(f, "{lhs}.{field} === {rhs}"),
            Constraint::Method(lhs, field, rhs) => write!(f, "{lhs}.{field}(..) === {rhs}"),
        }
    }
}

pub struct InferCtx<'mg, 'ty> {
    ctx: TyCtx<'ty>,
    next_id: Cell<u32>,
    constraints: Vec<Constraint<'ty>>,
    ty_vars: RefCell<Vec<TyVarId>>,
    md: &'mg ir::Module<'ty>,
}

impl<'mg, 'ty> Debug for InferCtx<'mg, 'ty> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "InferCtx {{")?;
        for constraint in &self.constraints {
            writeln!(f, "    {constraint}")?;
        }
        writeln!(f, "}}")
    }
}

impl<'mg, 'ty> InferCtx<'mg, 'ty> {
    pub fn new(md: &'mg ir::Module<'ty>) -> Self {
        InferCtx {
            ctx: md.ty_ctx(),
            next_id: Cell::new(0),
            constraints: Default::default(),
            ty_vars: Default::default(),
            md,
        }
    }

    fn mk_var_id(&self) -> TyVarId {
        let id = self.next_id.get();
        self.next_id.set(id + 1);
        let ty_var = TyVarId(id);
        self.ty_vars.borrow_mut().push(ty_var);
        ty_var
    }

    pub fn mk_var(&self) -> Ty<'ty> {
        self.ctx.int(TyKind::TyVar(self.mk_var_id()))
    }

    pub fn field(&mut self, expr: Ty<'ty>, field: String, ty: Ty<'ty>) -> InferResult<()> {
        let expected_adt = || ExpectedAdt(format!("{}", expr));
        match expr.full_deref_ty().0 .0 {
            TyKind::Adt(adt) => {
                if let Some(fty) = adt.get_field(self.md, &field) {
                    self.eq(ty, fty)?;
                }
            }

            TyKind::Pointer(..) => {
                panic!("Deref failed");
            }

            TyKind::Primitive(..)
            | TyKind::Param(..)
            | TyKind::Tuple(..)
            | TyKind::Fun(..)
            | TyKind::SizedArray(..)
            | TyKind::UnsizedArray(..)
            | TyKind::Range(..) => {
                return Err(expected_adt());
            }
            TyKind::TyVar(_) => self.constraints.push(Constraint::Field(expr, field, ty)),
            TyKind::Err => (),
        }
        Ok(())
    }

    pub fn method(&mut self, expr: Ty<'ty>, method: String, ty: Ty<'ty>) -> InferResult<()> {
        let expected_adt = || ExpectedAdt(format!("{}", expr));
        match expr.full_deref_ty().0 .0 {
            TyKind::Adt(adt) => {
                if let Some(mty) = adt.get_method_ty(self.md, &method) {
                    self.eq(ty, mty)?;
                }
            }
            TyKind::Param(..) => {
                todo!("Handle tyvar traits");
            }
            TyKind::Pointer(..) => {
                panic!("Deref failed");
            }
            TyKind::Primitive(..)
            | TyKind::Tuple(..)
            | TyKind::Fun(..)
            | TyKind::SizedArray(..)
            | TyKind::UnsizedArray(..)
            | TyKind::Range(..) => {
                return Err(expected_adt());
            }
            TyKind::TyVar(_) => self.constraints.push(Constraint::Method(expr, method, ty)),
            TyKind::Err => (),
        }
        Ok(())
    }

    pub fn eq(&mut self, lhs: Ty<'ty>, rhs: Ty<'ty>) -> InferResult<()> {
        let mismatch = || MismatchedTypes(format!("{} != {}", lhs, rhs));
        match (lhs.0 .0, rhs.0 .0) {
            (TyKind::Pointer(l_pt, l_inner), TyKind::Pointer(r_pt, r_inner)) => {
                if *l_pt != *r_pt {
                    Err(mismatch())
                } else {
                    self.eq(*l_inner, *r_inner)
                }
            }
            (TyKind::Tuple(l_tys), TyKind::Tuple(r_tys)) => {
                if l_tys.len() != r_tys.len() {
                    Err(mismatch())
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
                    Err(mismatch())
                } else {
                    for (lhs, rhs) in l_params.iter().zip(r_params) {
                        self.eq(*lhs, *rhs)?;
                    }
                    Ok(())
                }
            }
            (TyKind::SizedArray(l_size, l_inner), TyKind::SizedArray(r_size, r_inner)) => {
                if l_size != r_size {
                    Err(mismatch())
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
                    Err(mismatch())
                } else {
                    for (lhs, rhs) in l_ty_params.iter().zip(r_ty_params) {
                        self.eq(*lhs, *rhs)?;
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
                self.constraints.push(Constraint::Eq(lhs, rhs));
                Ok(())
            }
        }
    }

    pub fn check(&self, replacement: &HashMap<TyVarId, Ty<'ty>>) -> InferResult<()> {
        for constraint in &self.constraints {
            match constraint {
                Constraint::Eq(lhs, rhs) => {
                    let lhs = replace_ty_int(self.ctx, replacement, *lhs);
                    let rhs = replace_ty_int(self.ctx, replacement, *rhs);
                    if lhs != rhs {
                        panic!("{} != {}", lhs, rhs);
                    }
                }
                Constraint::Field(expr, field, ty) => {
                    let expr = replace_ty_int(self.ctx, replacement, *expr);
                    let ty = replace_ty_int(self.ctx, replacement, *ty);
                    if let TyKind::Adt(adt) = expr.full_deref_ty().0 .0 {
                        if let Some(fty) = adt.get_field(self.md, field) {
                            assert_eq!(ty, fty);
                        } else {
                            panic!("no such field");
                        }
                    } else {
                        panic!("Not struct type {}", expr);
                    }
                }
                Constraint::Method(expr, method, ty) => {
                    let expr = replace_ty_int(self.ctx, replacement, *expr);
                    let ty = replace_ty_int(self.ctx, replacement, *ty);
                    if let TyKind::Adt(adt) = expr.full_deref_ty().0 .0 {
                        if let Some(mty) = adt.get_method_ty(self.md, method) {
                            assert_eq!(ty, mty);
                        } else {
                            panic!("no such field");
                        }
                    } else {
                        panic!("Not struct type {}", expr);
                    }
                }
            }
        }
        Ok(())
    }
}

pub fn is_definite_ty(ty: Ty) -> bool {
    match ty.0 .0 {
        TyKind::Pointer(_, ty)
        | TyKind::Range(ty)
        | TyKind::SizedArray(_, ty)
        | TyKind::UnsizedArray(ty) => is_definite_ty(*ty),

        TyKind::Tuple(tys) | TyKind::Adt(AdtType { ty_params: tys, .. }) => {
            tys.iter().copied().all(is_definite_ty)
        }

        TyKind::Fun(tys, ty) => tys.iter().copied().all(is_definite_ty) && is_definite_ty(*ty),

        TyKind::TyVar(_) => false,
        TyKind::Primitive(_) | TyKind::Param(_) | TyKind::Err => true,
    }
}
