use either::Either;

use super::*;
use crate::ty;
use crate::{
    ir::UnaryOp,
    tir_lower::helpers::map_to_vec,
    ty::{AdtType, TyKind},
};

impl<'ty, 'mg> TirLower<'ty, 'mg> {
    pub fn expr(&mut self, expr: &tir::Expr<'ty>) -> LowerResult<ir::Expr<'ty>> {
        let span = expr.span().clone();
        let expr_ty = self.tir.get_ty(expr.id());
        let kind = match expr.kind() {
            tir::ExprKind::Integer(spec) => ir::ExprKind::Integer(*spec),
            tir::ExprKind::Float(spec) => ir::ExprKind::Float(*spec),
            tir::ExprKind::String(value) => ir::ExprKind::String(value.clone()),
            tir::ExprKind::Bool(value) => ir::ExprKind::Bool(*value),
            tir::ExprKind::Null => ir::ExprKind::Null,

            tir::ExprKind::Ident(name, generics) => {
                let value = self.resolve_value(&name, &generics);
                if value.is_none() {
                    self.err
                        .err(format!("Name `{}` not found in scope", span.str()), &span);
                    todo!("Return something idk");
                }
                let value = value.unwrap();
                match value {
                    Either::Left(varname) => ir::ExprKind::Ident(varname),
                    Either::Right(path) => {
                        ir::ExprKind::GlobalIdent(path.clone(), generics.clone())
                    }
                }
            }

            tir::ExprKind::Tuple(exprs) => {
                let exprs = map_to_vec(exprs, |expr| self.expr(expr))?;
                ir::ExprKind::Tuple(exprs)
            }

            tir::ExprKind::Assign(lhs, op, rhs) => {
                let lhs = Box::new(self.expr(lhs)?);
                let rhs = Box::new(self.expr(rhs)?);
                ir::ExprKind::Assign(lhs, *op, rhs)
            }

            tir::ExprKind::Binary(lhs, op, rhs) => {
                let lhs = Box::new(self.expr(lhs)?);
                let rhs = Box::new(self.expr(rhs)?);
                ir::ExprKind::Binary(lhs, *op, rhs)
            }

            tir::ExprKind::Unary(op, expr) => {
                let expr = Box::new(self.expr(expr)?);
                ir::ExprKind::Unary(*op, expr)
            }

            tir::ExprKind::Dot(lhs, rhs) => {
                let mut lhs = self.expr(lhs)?;
                while let TyKind::Pointer(_, inner) = self.md.ty_of(&lhs).0 .0 {
                    let span = lhs.span().clone();
                    lhs = self.md.mk_expr(
                        ir::ExprKind::Unary(UnaryOp::Deref, Box::new(lhs)),
                        span,
                        *inner,
                    );
                }
                ir::ExprKind::Dot(Box::new(lhs), rhs.clone())
            }

            tir::ExprKind::Cast(expr, ty) => {
                let expr = self.expr(expr)?;
                ir::ExprKind::Cast(Box::new(expr), *ty)
            }

            tir::ExprKind::Range(range) => todo!(),

            tir::ExprKind::Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                let condition = Box::new(self.expr(condition)?);
                let then_expr = Box::new(self.expr(then_expr)?);
                let else_expr = Box::new(self.expr(else_expr)?);
                ir::ExprKind::Ternary {
                    condition,
                    then_expr,
                    else_expr,
                }
            }

            tir::ExprKind::DotCall {
                expr,
                field,
                arguments,
            } => {
                let expr = self.expr(expr)?;
                let struct_ty = self.md.ty_of(&expr);
                let (method_ty, method_generics, method_def_id) =
                    if let TyKind::Adt(adt) = struct_ty.full_deref_ty().0 .0 {
                        adt.get_method_ty_and_def_id(self.md, field)
                            .expect("Invalid DotCall")
                    } else {
                        panic!()
                    };
                // TODO: coerce expr to correct reference type
                let expr = expr.coerce_ref(self.md, 0);
                let arguments = {
                    let mut out_args = Vec::with_capacity(arguments.len() + 1);
                    out_args.push(expr);
                    for arg in arguments {
                        out_args.push(self.expr(arg)?);
                    }
                    out_args
                };

                let method_path = self.md.get_path_by_def_id(method_def_id).clone();

                let expr = Box::new(self.md.mk_expr(
                    ir::ExprKind::GlobalIdent(method_path, method_generics),
                    span.clone(),
                    method_ty,
                ));

                ir::ExprKind::Call { expr, arguments }
            }

            tir::ExprKind::Call { expr, arguments } => {
                let arguments = map_to_vec(arguments, |expr| self.expr(expr))?;
                let expr = Box::new(self.expr(expr)?);
                ir::ExprKind::Call { expr, arguments }
            }

            tir::ExprKind::Index { expr, index } => {
                let _expr = Box::new(self.expr(expr)?);
                let _index = Box::new(self.expr(index)?);
                todo!("Indexing requires slices and maybe some polymorphism of some kind");
            }

            tir::ExprKind::Array { members } => {
                let members = map_to_vec(members, |expr| self.expr(expr))?;
                ir::ExprKind::Array { members }
            }

            tir::ExprKind::Struct { members, .. } => {
                let members = map_to_vec(members, |(name, expr)| {
                    Ok((name.clone(), Box::new(self.expr(expr)?)))
                })?;
                ir::ExprKind::Struct {
                    ty: expr_ty,
                    members,
                }
            }
        };
        Ok(self.md.mk_expr(kind, span, expr_ty))
    }
}
