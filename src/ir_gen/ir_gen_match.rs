use crate::generics::replace_generics;
use crate::ir;
use crate::ir_gen::*;

#[derive(Debug, Clone)]
enum CasePattern<'ty> {
    Variant(ty::Ty<'ty>, ir::Path, String, Box<CasePattern<'ty>>),
    Tuple(ty::Ty<'ty>, Vec<CasePattern<'ty>>),
    Ident(ty::Ty<'ty>, String),
}

impl<'ty, 'mg> IrGen<'ty, 'mg> {
    fn to_case_pattern(
        &self,
        ty: ty::Ty<'ty>,
        pat: &ast::Spanned<ast::Pattern>,
    ) -> Result<CasePattern<'ty>, ModGenError> {
        let pat = match pat.value() {
            ast::Pattern::Variant(name, _, params, _) => {
                let name = self.gen_path(name.value())?;
                assert!(matches!(ty, ty::Ty(Int(ty::TyKind::Adt(_)))));
                let ty_param_tys =
                    if let ty::Ty(Int(ty::TyKind::Adt(ty::AdtType { ty_params, .. }))) = ty {
                        ty_params
                    } else {
                        panic!()
                    };
                let (_, cons_params, ty_param_names) = if let Some(ir::Def {
                    kind:
                        ir::DefKind::Fun {
                            external: ir::ExternKind::VariantConstructor,
                            params: cons_params,
                            return_type,
                            ty_params,
                        },
                    ..
                }) = &self.module.get_def_by_path(&name)
                {
                    assert_eq!(cons_params.len(), params.len());
                    (return_type, cons_params, ty_params)
                } else {
                    todo!("error")
                    // ERR_TY
                };

                assert_eq!(ty_param_names.len(), ty_param_tys.len());
                let generics = ty_param_names
                    .iter()
                    .cloned()
                    .zip(ty_param_tys.iter().cloned())
                    .collect::<Vec<_>>();
                let ty = replace_generics(self.module.ty_ctx(), ty, &generics);
                // ty_param
                let enum_name = name.pop_end().unwrap();
                let variant_name = name.end().clone();

                let params = params.iter().zip(cons_params.iter());
                let (tys, params) = {
                    let mut out = Vec::with_capacity(cons_params.len());
                    let mut tys = Vec::with_capacity(cons_params.len());
                    for (pat, (_, ty)) in params {
                        let ty = replace_generics(self.module.ty_ctx(), *ty, &generics);
                        tys.push(ty);
                        out.push(self.to_case_pattern(ty, pat)?);
                    }
                    (tys, out)
                };

                let tuple_ty = ty::TyKind::Tuple(tys);
                let tuple_ty = self.module.ty_ctx().int(tuple_ty);

                let tuple_ty = replace_generics(self.module.ty_ctx(), tuple_ty, &generics);

                CasePattern::Variant(
                    ty,
                    enum_name,
                    variant_name,
                    Box::new(CasePattern::Tuple(tuple_ty, params)),
                )
            }
            ast::Pattern::Tuple(_, params, _) => {
                let tys = if let ty::Ty(Int(ty::TyKind::Tuple(params))) = ty {
                    params
                } else {
                    panic!()
                };
                let params = params.iter().zip(tys.iter());
                let params = {
                    let mut out = Vec::with_capacity(tys.len());
                    for (pat, ty) in params {
                        out.push(self.to_case_pattern(*ty, pat)?);
                    }
                    out
                };

                CasePattern::Tuple(ty, params)
            }
            ast::Pattern::Ident(name) => {
                let name = self.gen_path(name.value())?;
                if let Some(ir::Def {
                    kind:
                        ir::DefKind::Fun {
                            external: ir::ExternKind::VariantConstructor,
                            params: cons_params,
                            return_type,
                            ..
                        },
                    ..
                }) = &self.module.get_def_by_path(&name)
                {
                    let enum_name = name.pop_end().unwrap();
                    let variant_name = name.end().clone();
                    assert_eq!(cons_params.len(), 0);
                    CasePattern::Variant(
                        ty,
                        enum_name,
                        variant_name,
                        Box::new(CasePattern::Tuple(*return_type, Vec::new())),
                    )
                } else if let ir::Path::Terminal(name) = name {
                    CasePattern::Ident(ty, name)
                } else {
                    todo!()
                }
            }
        };
        Ok(pat)
    }
    pub fn gen_case(
        &mut self,
        expr: &ast::Spanned<ast::Expr>,
        arms: &ast::SpanSlice<ast::Arm>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
        let expr = self.gen_expr(expr)?;
        let span = expr.span().clone();
        let ty = expr.ty();

        let mut stmts = Vec::new();

        let pattern_var = self.declare_hidden_var(expr.ty());
        let pattern_var = ir::Expr::new(
            ir::ExprKind::Ident(pattern_var),
            expr.span().clone(),
            expr.ty(),
        );

        stmts.push(ir::Stmt::new(
            ir::StmtKind::Expr(Box::new(ir::Expr::new(
                ir::ExprKind::Assign(
                    Box::new(pattern_var.clone()),
                    ir::AssignOp::Eq,
                    Box::new(expr),
                ),
                span.clone(),
                ty,
            ))),
            span.clone(),
        ));

        let mut cases = Vec::new();

        for arm in arms {
            let pattern = self.to_case_pattern(ty, arm.value.pattern.as_ref())?;

            match pattern {
                CasePattern::Variant(_ty, enum_name, variant_name, inner) => {
                    if let CasePattern::Tuple(ty, members) = inner.as_ref() {
                        let mut stmts = Vec::new();
                        self.open_scope();
                        if !members.is_empty() {
                            let variant_var = self.declare_hidden_var(*ty);
                            let variant_var =
                                ir::Expr::new(ir::ExprKind::Ident(variant_var), span.clone(), *ty);
                            stmts.push(ir::Stmt::new(
                                ir::StmtKind::Expr(Box::new(ir::Expr::new(
                                    ir::ExprKind::Assign(
                                        Box::new(variant_var.clone()),
                                        ir::AssignOp::Eq,
                                        Box::new(ir::Expr::new(
                                            ir::ExprKind::Dot(
                                                Box::new(pattern_var.clone()),
                                                variant_name.clone(),
                                            ),
                                            span.clone(),
                                            *ty,
                                        )),
                                    ),
                                    span.clone(),
                                    *ty,
                                ))),
                                span.clone(),
                            ));
                            for (i, member) in members.iter().enumerate() {
                                if let CasePattern::Ident(id_ty, name) = member {
                                    let name = self.declare_var(name, *id_ty);
                                    let value_var = ir::Expr::new(
                                        ir::ExprKind::Ident(name.clone()),
                                        span.clone(),
                                        *id_ty,
                                    );
                                    stmts.push(ir::Stmt::new(
                                        ir::StmtKind::Expr(Box::new(ir::Expr::new(
                                            ir::ExprKind::Assign(
                                                Box::new(value_var.clone()),
                                                ir::AssignOp::Eq,
                                                Box::new(ir::Expr::new(
                                                    ir::ExprKind::Dot(
                                                        Box::new(variant_var.clone()),
                                                        format!("_{}", i),
                                                    ),
                                                    span.clone(),
                                                    *id_ty,
                                                )),
                                            ),
                                            span.clone(),
                                            *id_ty,
                                        ))),
                                        span.clone(),
                                    ));
                                } else {
                                    todo!()
                                }
                            }
                        }

                        let discriminant_expr = ir::Expr::new(
                            // HACK: shouldn't codegen here
                            ir::ExprKind::Ident(format!(
                                "{}_{}_k",
                                crate::codegen::mangle_path(&enum_name),
                                variant_name
                            )),
                            span.clone(),
                            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::I32),
                        );

                        stmts.reserve(arm.value().stmts.len());
                        for stmt in &arm.value().stmts {
                            stmts.push(self.gen_stmt(stmt)?);
                        }

                        self.close_scope();

                        let block_expr = ir::Stmt::new(ir::StmtKind::Block(stmts), span.clone());
                        cases.push((Box::new(discriminant_expr), Box::new(block_expr)));
                    } else {
                        panic!()
                    };
                }
                _ => todo!(),
            }
        }

        let expr = ir::Expr::new(
            ir::ExprKind::Dot(Box::new(pattern_var), "kind".into()),
            span.clone(),
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::I32),
        );

        stmts.push(ir::Stmt::new(
            ir::StmtKind::Switch {
                expr: Box::new(expr),
                cases,
                default: None,
            },
            span,
        ));

        Ok(ir::StmtKind::Block(stmts))
    }
}
