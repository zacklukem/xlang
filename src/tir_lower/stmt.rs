use super::*;

use crate::ir::AssignOp;
use crate::tir_lower::helpers::{break_label, continue_label, map_to_vec};

impl<'ty, 'mg> TirLower<'ty, 'mg> {
    pub fn stmt(&mut self, stmt: &tir::Stmt<'ty>) -> LowerResult<ir::Stmt<'ty>> {
        let span = stmt.span().clone();
        let label_next = self.label_next.take();
        let kind = match stmt.kind() {
            tir::StmtKind::Case { expr, arms } => self.gen_case_stmt(stmt, expr.as_ref(), &arms)?,

            tir::StmtKind::Let {
                mutable,
                pattern,
                type_name,
                expr,
            } => self.gen_let_stmt(stmt, *mutable, pattern.as_ref(), *type_name, expr.as_ref())?,

            tir::StmtKind::ForRange {
                label: _,
                initializer: _,
                range: _,
                block: _,
            } => todo!(),

            tir::StmtKind::If {
                condition,
                block,
                else_block,
            } => {
                let condition = Box::new(self.expr(condition)?);
                let block = Box::new(self.stmt(block)?);
                let else_block = else_block
                    .as_ref()
                    .map(|block| self.stmt(block))
                    .transpose()?
                    .map(Box::new);
                ir::StmtKind::If {
                    condition,
                    block,
                    else_block,
                }
            }

            tir::StmtKind::While {
                label,
                condition,
                block,
            } => {
                let label_prefix = label
                    .as_ref()
                    .cloned()
                    .unwrap_or_else(|| format!("while_{}", self.get_var_id()));

                self.continue_break_label.push(label_prefix.clone());
                let condition = Box::new(self.expr(condition)?);
                let block = Box::new(self.stmt(block)?);
                let popped_prefix = self.continue_break_label.pop().unwrap();
                assert_eq!(popped_prefix, label_prefix);

                let stmt = ir::StmtKind::While { condition, block };
                let stmt = ir::StmtKind::Labeled(
                    continue_label(&label_prefix),
                    Some(Box::new(ir::Stmt::new(stmt, span.clone()))),
                );
                self.label_next(break_label(&label_prefix));
                stmt
            }

            tir::StmtKind::Loop { label, block } => {
                let label_prefix = label
                    .as_ref()
                    .cloned()
                    .unwrap_or_else(|| format!("loop_{}", self.get_var_id()));

                self.continue_break_label.push(label_prefix.clone());

                let condition = Box::new(self.md.mk_const_bool(true, span.clone()));

                let block = Box::new(self.stmt(block)?);
                let popped_prefix = self.continue_break_label.pop().unwrap();

                assert_eq!(popped_prefix, label_prefix);

                let stmt = ir::StmtKind::While { condition, block };
                let stmt = ir::StmtKind::Labeled(
                    continue_label(&label_prefix),
                    Some(Box::new(ir::Stmt::new(stmt, span.clone()))),
                );
                self.label_next(break_label(&label_prefix));
                stmt
            }

            tir::StmtKind::InlineC {
                inputs,
                outputs,
                code,
            } => {
                let inputs = inputs
                    .iter()
                    .map(|(pt, varname, replace_name)| {
                        let varname = match pt {
                            ir::InlineCParamType::Var => {
                                self.scope.resolve(varname).unwrap().clone()
                            }
                            _ => varname.clone(),
                        };
                        (*pt, varname, replace_name.clone())
                    })
                    .collect();
                let outputs = outputs
                    .iter()
                    .map(|(replace_name, pt, varname)| {
                        let varname = self.scope.resolve(varname).unwrap();
                        (replace_name.clone(), *pt, varname.clone())
                    })
                    .collect();
                let code = code.clone();
                ir::StmtKind::InlineC {
                    inputs,
                    outputs,
                    code,
                }
            }

            tir::StmtKind::Block(stmts) => self.in_scope(|this| {
                let mut stmts = map_to_vec(stmts, |stmt| this.stmt(stmt))?;
                let label_next = std::mem::take(&mut this.label_next);
                if let Some(label) = label_next {
                    stmts.push(ir::Stmt::new(
                        ir::StmtKind::Labeled(label, None),
                        span.clone(),
                    ))
                }
                Ok(ir::StmtKind::Block(stmts))
            })?,

            tir::StmtKind::Return(Some(expr)) => {
                ir::StmtKind::Return(Some(Box::new(self.expr(expr)?)))
            }
            tir::StmtKind::Return(None) => ir::StmtKind::Return(None),

            tir::StmtKind::Continue(label) => {
                let label = if let Some(label) = label {
                    let label_exists = self.continue_break_label.contains(&label);
                    if !label_exists {
                        self.err
                            .err(format!("The label `{}` is not in scope", label), &span);
                        "err_placeholder".to_owned()
                    } else {
                        label.clone()
                    }
                } else {
                    let label = self.continue_break_label.last().map(|v| continue_label(v));
                    if let Some(label) = label {
                        label
                    } else {
                        self.err
                            .err("You must be in a loop to continue".into(), &span);
                        "err_placeholder".to_owned()
                    }
                };
                ir::StmtKind::Goto(label)
            }
            tir::StmtKind::Break(label) => {
                let label = if let Some(label) = label {
                    let label_exists = self.continue_break_label.contains(&label);
                    if !label_exists {
                        self.err
                            .err(format!("The label `{}` is not in scope", label), &span);
                        "err_placeholder".to_owned()
                    } else {
                        label.clone()
                    }
                } else {
                    let label = self.continue_break_label.last().map(|v| break_label(v));
                    if let Some(label) = label {
                        label
                    } else {
                        self.err.err("You must be in a loop to break".into(), &span);
                        "err_placeholder".to_owned()
                    }
                };
                ir::StmtKind::Goto(label)
            }
            tir::StmtKind::Expr(expr) => {
                let expr = Box::new(self.expr(expr)?);
                ir::StmtKind::Expr(expr)
            }
        };
        let stmt = ir::Stmt::new(kind, span.clone());

        if let Some(label) = label_next {
            Ok(ir::Stmt::new(
                ir::StmtKind::Labeled(label, Some(Box::new(stmt))),
                span,
            ))
        } else {
            Ok(stmt)
        }
    }

    fn gen_let_stmt(
        &mut self,
        _stmt: &tir::Stmt<'ty>,
        _mutable: bool,
        pattern: &tir::Pattern,
        _type_name: Option<Ty<'ty>>,
        expr: &tir::Expr<'ty>,
    ) -> LowerResult<ir::StmtKind<'ty>> {
        let id = if let tir::PatternKind::Ident(id) = &pattern.1 {
            id
        } else {
            todo!("Let destructure");
        };
        let expr = self.expr(expr)?;
        let expr_ty = self.md.ty_of(&expr);
        let varname = self.declare_var(id, expr_ty);
        let assign_expr = self.md.mk_assign_expr(
            self.md.mk_var_expr(varname, pattern.0.clone(), expr_ty),
            AssignOp::Eq,
            expr,
        );
        Ok(assign_expr.stmt_kind())
    }
}
