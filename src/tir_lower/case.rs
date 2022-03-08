use log::debug;

use crate::generics::replace_generics;
use crate::ir::AssignOp;
use crate::ty::{self, AdtType, PrimitiveType, TyKind};

use super::*;

impl<'ty, 'mg> TirLower<'ty, 'mg> {
    pub fn gen_case_stmt(
        &mut self,
        stmt: &tir::Stmt<'ty>,
        expr: &tir::Expr<'ty>,
        arms: &[tir::Arm<'ty>],
    ) -> LowerResult<ir::StmtKind<'ty>> {
        let stmt_span = stmt.span().clone();
        let expr = self.expr(expr)?;
        let expr_ty = self.md.ty_of(&expr);

        debug!("{expr_ty}");

        let (enum_path, ty_param_tys) = match expr_ty.0 .0 {
            TyKind::Adt(AdtType {
                path, ty_params, ..
            }) => (path, ty_params),
            _ => todo!(),
        };

        let mut stmts = Vec::new();

        // Create a variable for the case input
        let expr_varname = self.declare_hidden_var(expr_ty);
        let expr_span = expr.span().clone();
        // This is the actual expr that should be used
        macro_rules! expr_var {
            () => {
                self.md
                    .mk_var_expr(expr_varname.clone(), expr_span.clone(), expr_ty)
            };
        }
        // Assign the variable
        stmts.push(
            self.md
                .mk_assign_expr(expr_var!(), AssignOp::Eq, expr)
                .stmt(),
        );

        let mut cases = Vec::new();

        for arm in arms {
            if let tir::PatternKind::Variant(path, pattern) = arm.pattern.kind() {
                if let tir::PatternKind::Tuple(patterns) = pattern.kind() {
                    let def = self.md.get_def_by_path(path);
                    let variant_name = path.end();
                    if let Some(ir::DefKind::Fun {
                        ty_params,
                        return_type,
                        params,
                        ..
                    }) = def.map(ir::Def::kind)
                    {
                        let generics: Vec<_> = ty_params
                            .iter()
                            .cloned()
                            .zip(ty_param_tys.iter().copied())
                            .collect();
                        debug!("case arm generics: {:?}", generics);
                        let tuple_ty = self
                            .tcx
                            .int(TyKind::Tuple(params.iter().map(|(_, ty)| *ty).collect()));
                        let tuple_ty = replace_generics(self.tcx, tuple_ty, &generics);
                        // The value of the discriminant (e.g. maybe_Maybe_k)
                        let discriminant_value = self.md.mk_expr(
                            ir::ExprKind::DiscriminantValue(path.clone()),
                            arm.pattern.span().clone(),
                            ty::primitive_ty(self.tcx, PrimitiveType::USize),
                        );
                        macro_rules! variant_tuple_get {
                            ($i:expr, $ty:expr) => {{
                                let variant_tuple = self.md.mk_expr(
                                    ir::ExprKind::GetVariant(
                                        Box::new(expr_var!()),
                                        variant_name.clone(),
                                    ),
                                    expr_span.clone(),
                                    tuple_ty,
                                );
                                self.md.mk_expr(
                                    ir::ExprKind::TupleValue(Box::new(variant_tuple), $i),
                                    expr_span.clone(),
                                    $ty,
                                )
                            }};
                        }
                        let stmt = self.in_scope(|this| {
                            let mut stmts = Vec::new();
                            assert!(params.len() <= 0xff);
                            // Bind each element of the tuple pattern
                            for (i, ((_, ty), pattern)) in params.iter().zip(patterns).enumerate() {
                                let ty = replace_generics(this.tcx, *ty, &generics);
                                if let tir::PatternKind::Ident(id) = pattern.kind() {
                                    let varname = this.declare_var(id, ty);
                                    stmts.push(
                                        this.md
                                            .mk_assign_expr(
                                                this.md.mk_var_expr(
                                                    varname,
                                                    pattern.span().clone(),
                                                    ty,
                                                ),
                                                AssignOp::Eq,
                                                variant_tuple_get!(i as u8, ty),
                                            )
                                            .stmt(),
                                    );
                                } else {
                                    todo!()
                                }
                            }
                            stmts.reserve(arm.stmts.len());
                            for stmt in &arm.stmts {
                                stmts.push(this.stmt(stmt)?);
                            }
                            Ok(ir::Stmt::new(ir::StmtKind::Block(stmts), expr_span.clone()))
                        })?;
                        cases.push((discriminant_value, stmt));
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                }
            } else {
                todo!()
            }
        }

        let expr = self.md.mk_expr(
            ir::ExprKind::Discriminant(Box::new(expr_var!())),
            expr_span,
            ty::primitive_ty(self.tcx, PrimitiveType::USize),
        );

        stmts.push(ir::Stmt::new(
            ir::StmtKind::Switch {
                expr: Box::new(expr),
                cases,
                default: None,
            },
            stmt_span,
        ));

        Ok(ir::StmtKind::StmtList(stmts))
    }
}
