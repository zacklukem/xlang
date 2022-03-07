use super::*;
use crate::ast::Span;
use crate::ir::AssignOp;
use crate::tir_lower::helpers::map_to_vec;

fn continue_label(v: &str) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &str) -> String {
    format!("{}_break", v)
}

impl<'ty, 'mg> TirLower<'ty, 'mg> {
    pub fn stmt(&mut self, stmt: &tir::Stmt<'ty>) -> LowerResult<ir::Stmt<'ty>> {
        let span = stmt.span().clone();
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
                let (inputs, outputs, code) = (inputs.clone(), outputs.clone(), code.clone());
                ir::StmtKind::InlineC {
                    inputs,
                    outputs,
                    code,
                }
            }

            tir::StmtKind::Block(stmts) => {
                let stmts = map_to_vec(stmts, |stmt| self.stmt(stmt))?;
                ir::StmtKind::Block(stmts)
            }

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
        Ok(ir::Stmt::new(kind, span))
    }

    fn gen_case_stmt(
        &mut self,
        stmt: &tir::Stmt<'ty>,
        expr: &tir::Expr<'ty>,
        arms: &[tir::Arm<'ty>],
    ) -> LowerResult<ir::StmtKind<'ty>> {
        // todo!()
        Ok(ir::StmtKind::Labeled("asdfasdfasdf".to_string(), None))
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
