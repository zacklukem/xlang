use crate::ast;
use crate::error_context::ErrorContext;
use crate::ir;
use crate::symbol as sym;
use crate::type_check::TypeCheckerError;
use std::collections::HashMap;

pub fn gen_fun_block<'tyc>(
    module: &'tyc ir::Module,
    err: &'tyc mut ErrorContext,
    name: &sym::Name,
    params: &Vec<(String, sym::Type)>,
    return_type: &sym::Type,
    fun: &ast::SpanBox<ast::FunBlock>,
) -> Result<ir::Fun, TypeCheckerError> {
    let mut variable_defs = HashMap::new();
    let mut ir_gen = IrGen {
        var_id: 0,
        module,
        err,
        scope: Box::new(Scope::default()),
        variable_defs: &mut variable_defs,
        continue_break_label: Default::default(),
        label_next: None,
    };
    let body = ir_gen.gen_fun_block(name, params, return_type, fun)?;
    Ok(ir::Fun {
        name: name.clone(),
        block: body,
        variable_defs: variable_defs
            .iter()
            .map(|(a, b)| (a.clone(), b.clone()))
            .collect(),
    })
}

#[derive(Debug, Default)]
struct Scope {
    parent: Option<Box<Scope>>,
    /// Maps <String: block-scoped var name> to <String: function-scoped var name>
    variables: HashMap<String, String>,
}

impl Scope {
    fn resolve(&self, name: &String) -> Option<&String> {
        match self.variables.get(name) {
            Some(v) => Some(v),
            None => match &self.parent {
                Some(parent) => parent.resolve(name),
                None => None,
            },
        }
    }

    fn insert(&mut self, block_scope_name: String, fun_scope_name: String) -> Option<String> {
        self.variables.insert(block_scope_name, fun_scope_name)
    }
}

struct IrGen<'a, 'tyc> {
    var_id: u32,
    module: &'tyc ir::Module,
    err: &'tyc mut ErrorContext,
    scope: Box<Scope>,
    /// types of variables (variable scoped)
    variable_defs: &'a mut HashMap<String, sym::Type>,
    continue_break_label: Vec<String>,
    label_next: Option<String>,
}

fn continue_label(v: &String) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &String) -> String {
    format!("{}_break", v)
}

impl<'a, 'tyc> IrGen<'a, 'tyc> {
    fn get_var_id(&mut self) -> u32 {
        let n = self.var_id;
        self.var_id += 1;
        n
    }

    fn open_scope(&mut self) {
        let old_scope = std::mem::take(&mut self.scope);
        self.scope.parent = Some(old_scope);
    }

    fn close_scope(&mut self) {
        let parent = std::mem::take(&mut self.scope.parent);
        self.scope = parent.unwrap();
    }

    fn declare_var(&mut self, block_scope_name: &String, ty: sym::Type) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", block_scope_name, id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        self.scope
            .insert(block_scope_name.clone(), fun_scope_name.clone());
        fun_scope_name
    }

    fn declare_hidden_var(&mut self, ty: sym::Type) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", "hidden", id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        fun_scope_name
    }

    fn label_next(&mut self, label: String) {
        assert!(self.label_next.is_none());
        self.label_next = Some(label);
    }

    fn resolve(&'a self, name: &ast::Name) -> Option<sym::Type> {
        if let ast::Name::Ident(ast::Ident { span }) = name {
            let id = span.str().into();
            if let Some(var) = self.scope.resolve(&id) {
                return self.variable_defs.get(var).map(sym::Type::clone);
            }
        }
        let name = name.into();
        match self.module.ty_ctx.root.resolve(&name) {
            Some(sym::SymbolInfo {
                symbol: sym::Symbol::Struct { .. },
                ..
            }) => Some(sym::Type::Named(name)),

            Some(sym::SymbolInfo {
                symbol:
                    sym::Symbol::Fun {
                        params,
                        return_type,
                    },
                ..
            }) => Some(sym::Type::Fun(
                params.iter().map(|(_, t)| t.clone()).collect(),
                return_type.clone(),
            )),

            _ => None,
        }
    }

    fn gen_fun_block(
        &mut self,
        name: &sym::Name,
        params: &Vec<(String, sym::Type)>,
        return_type: &sym::Type,
        body: &ast::SpanBox<ast::FunBlock>,
    ) -> Result<ir::Stmt, TypeCheckerError> {
        let mut stmts = Vec::new();
        for stmt in &body.value().stmts {
            stmts.push(self.gen_stmt(stmt)?);
        }
        let label_next = std::mem::take(&mut self.label_next);
        if let Some(label) = label_next {
            stmts.push(ir::Stmt::new(
                ir::StmtKind::Labeled(label, None),
                body.span.clone(),
            ))
        }
        Ok(ir::Stmt::new(ir::StmtKind::Block(stmts), body.span.clone()))
    }

    fn gen_block(
        &mut self,
        body: &ast::SpanVec<ast::Stmt>,
        close_brace: &ast::Span,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        self.open_scope();
        let mut stmts = Vec::new();
        for stmt in body {
            stmts.push(self.gen_stmt(stmt)?);
        }
        let label_next = std::mem::take(&mut self.label_next);
        if let Some(label) = label_next {
            stmts.push(ir::Stmt::new(
                ir::StmtKind::Labeled(label, None),
                close_brace.clone(),
            ))
        }
        self.close_scope();
        Ok(ir::StmtKind::Block(stmts))
    }

    fn gen_if_stmt(
        &mut self,
        condition: &ast::Spanned<ast::Expr>,
        block: &ast::Spanned<ast::Stmt>,
        else_block: Option<&ast::SpanBox<ast::Stmt>>,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        let condition = Box::new(self.gen_expr(condition)?);
        let block = Box::new(self.gen_stmt(block)?);
        let else_block = else_block
            .map(|v| self.gen_stmt(v).map(Box::new))
            .transpose()?;
        Ok(ir::StmtKind::If {
            condition,
            block,
            else_block,
        })
    }

    fn gen_while_stmt(
        &mut self,
        span: &ast::Span,
        label: Option<&ast::Ident>,
        condition: &ast::Spanned<ast::Expr>,
        block: &ast::Spanned<ast::Stmt>,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        let label_prefix = label
            .map(|v| v.str().into())
            .unwrap_or_else(|| format!("while_{}", self.get_var_id()));

        self.continue_break_label.push(label_prefix.clone());
        let condition = Box::new(self.gen_expr(condition)?);
        let block = Box::new(self.gen_stmt(block)?);
        let popped_prefix = self.continue_break_label.pop().unwrap();
        assert_eq!(popped_prefix, label_prefix);

        let stmt = ir::StmtKind::While { condition, block };
        let stmt = ir::StmtKind::Labeled(
            continue_label(&label_prefix),
            Some(Box::new(ir::Stmt::new(stmt, span.clone()))),
        );
        self.label_next(break_label(&label_prefix));
        Ok(stmt)
    }

    fn gen_loop_stmt(
        &mut self,
        span: &ast::Span,
        label: Option<&ast::Ident>,
        block: &ast::Spanned<ast::Stmt>,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        let label_prefix = label
            .map(|v| v.str().into())
            .unwrap_or_else(|| format!("loop_{}", self.get_var_id()));

        self.continue_break_label.push(label_prefix.clone());

        let condition = Box::new(ir::Expr::new(
            ir::ExprKind::Bool(true),
            span.clone(),
            sym::Type::Primitive(sym::PrimitiveType::Bool),
        ));

        let block = Box::new(self.gen_stmt(block)?);
        let popped_prefix = self.continue_break_label.pop().unwrap();

        assert_eq!(popped_prefix, label_prefix);

        let stmt = ir::StmtKind::While { condition, block };
        let stmt = ir::StmtKind::Labeled(
            continue_label(&label_prefix),
            Some(Box::new(ir::Stmt::new(stmt, span.clone()))),
        );
        self.label_next(break_label(&label_prefix));
        Ok(stmt)
    }
    // gen_for_range_stmt

    fn gen_let_stmt_patterned(
        &mut self,
        out: &mut Vec<ir::StmtKind>,
        span: &ast::Span,
        pattern: &ast::Spanned<ast::Pattern>,
        ty: sym::Type,
        expr: ir::Expr,
    ) -> Result<(), TypeCheckerError> {
        match pattern.value() {
            ast::Pattern::Tuple(_, patterns, _) => {
                let global_var_name = self.declare_hidden_var(ty.clone());
                let lhs_expr = ir::ExprKind::Ident(sym::Name::Ident(global_var_name.clone()));
                let lhs_expr = ir::Expr::new(lhs_expr, span.clone(), ty.clone()).lhs_expr();
                let assign_expr = ir::Expr::new(
                    ir::ExprKind::Assign(Box::new(lhs_expr), ir::AssignOp::Eq, Box::new(expr)),
                    span.clone(),
                    ty.clone(),
                );
                out.push(ir::StmtKind::Expr(Box::new(assign_expr)));

                if let sym::Type::Tuple(tys) = &ty {
                    if tys.len() != patterns.len() {
                        self.err.err("Incompatible pattern types".into(), span);
                    }
                    for (i, (pattern, pat_ty)) in patterns.iter().zip(tys.iter()).enumerate() {
                        let access_expr =
                            ir::ExprKind::Ident(sym::Name::Ident(global_var_name.clone()));
                        let access_expr = ir::Expr::new(access_expr, span.clone(), ty.clone());

                        let expr = ir::ExprKind::Dot(Box::new(access_expr), format!("_{}", i));
                        let expr = ir::Expr::new(expr, span.clone(), pat_ty.clone());

                        self.gen_let_stmt_patterned(out, span, pattern, pat_ty.clone(), expr)?;
                    }
                } else {
                    self.err.err("Incompatible pattern types".into(), span);
                }
            }
            ast::Pattern::Ident(id) => {
                let global_var_name = self.declare_var(&id.str().into(), ty.clone());
                let lhs_expr = ir::ExprKind::Ident(sym::Name::Ident(global_var_name));
                let lhs_expr = ir::Expr::new(lhs_expr, id.span.clone(), ty.clone()).lhs_expr();
                let assign_expr = ir::Expr::new(
                    ir::ExprKind::Assign(Box::new(lhs_expr), ir::AssignOp::Eq, Box::new(expr)),
                    span.clone(),
                    ty,
                );
                out.push(ir::StmtKind::Expr(Box::new(assign_expr)));
            }
        }
        Ok(())
    }

    fn gen_let_stmt(
        &mut self,
        span: &ast::Span,
        pattern: &ast::Spanned<ast::Pattern>,
        ty: Option<&ast::SpanBox<ast::Type>>,
        expr: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        // let (a,b,(c,d)) = ...;
        // Generates:
        // let out: (A,B,(C,D)) = ...;
        // let a: A = out.0;
        // let b: B = out.1;
        // let inner: (C,D) = out.2;
        // let c: C = inner.0;
        // let d: D = inner.1;

        let mut stmts = Vec::new();
        let expr = self.gen_expr(expr)?;
        let ty = if let Some(ty) = ty {
            todo!("Check expr - ty equality");
        } else {
            expr.ty().clone()
        };
        self.gen_let_stmt_patterned(&mut stmts, span, pattern, ty, expr)?;

        let stmts = stmts
            .into_iter()
            .map(|s| ir::Stmt::new(s, span.clone()))
            .collect();

        Ok(ir::StmtKind::StmtList(stmts))
    }

    fn gen_break_continue(
        &mut self,
        is_break: bool,
        span: &ast::Span,
        label: Option<&ast::Ident>,
    ) -> Result<ir::StmtKind, TypeCheckerError> {
        let map_fn = if is_break {
            break_label
        } else {
            continue_label
        };

        let label = if let Some(ident) = label {
            let label = ident.span.str().into();
            let label_exists = self.continue_break_label.contains(&label);
            if !label_exists {
                self.err.err(
                    format!("The label `{}` is not in scope", label),
                    &ident.span,
                );
                "err_placeholder".into()
            } else {
                label
            }
        } else {
            let label = self.continue_break_label.last().map(map_fn);
            if let Some(label) = label {
                label.clone()
            } else {
                self.err
                    .err("You must be in a loop to break or continue".into(), span);
                "err_placeholder".into()
            }
        };
        Ok(ir::StmtKind::Goto(label))
    }

    fn gen_stmt(&mut self, stmt: &ast::Spanned<ast::Stmt>) -> Result<ir::Stmt, TypeCheckerError> {
        let label_next = std::mem::take(&mut self.label_next);
        let stmt_kind = match stmt.value() {
            ast::Stmt::If {
                condition,
                block,
                else_block,
                ..
            } => self.gen_if_stmt(condition.as_ref(), block.as_ref(), else_block.as_ref())?,

            ast::Stmt::While {
                label,
                condition,
                block,
                ..
            } => self.gen_while_stmt(
                &stmt.span,
                label.as_ref(),
                condition.as_ref(),
                block.as_ref(),
            )?,

            ast::Stmt::Loop { label, block, .. } => {
                self.gen_loop_stmt(&stmt.span, label.as_ref(), block.as_ref())?
            }

            ast::Stmt::ForRange {
                label,
                initializer,
                range,
                block,
                ..
            } => todo!(),

            ast::Stmt::Let {
                pattern,
                type_name,
                expr,
                ..
            } => self.gen_let_stmt(
                &stmt.span,
                pattern.as_ref(),
                type_name.as_ref(),
                expr.as_ref(),
            )?,

            ast::Stmt::Block(_, stmts, close_brace) => self.gen_block(stmts, close_brace)?,
            ast::Stmt::Return(_, expr) => todo!(),
            ast::Stmt::Continue(span, label) => {
                self.gen_break_continue(false, span, label.as_ref())?
            }
            ast::Stmt::Break(span, label) => self.gen_break_continue(true, span, label.as_ref())?,

            ast::Stmt::Expr(expr) => todo!(),
        };
        let span = stmt.span.clone();
        let stmt = ir::Stmt::new(stmt_kind, span.clone());
        match label_next {
            Some(label) => Ok(ir::Stmt::new(
                ir::StmtKind::Labeled(label, Some(Box::new(stmt))),
                span,
            )),
            None => Ok(stmt),
        }
    }

    fn gen_expr(&mut self, expr: &ast::Spanned<ast::Expr>) -> Result<ir::Expr, TypeCheckerError> {
        let span = &expr.span;
        let expr = match expr.value() {
            ast::Expr::Integer(span, _) => {
                let value = str::parse::<i64>(span.str()).unwrap();
                let kind = ir::ExprKind::Integer(ir::IntegerSpecifier::I64(value));
                ir::Expr::new(
                    kind,
                    expr.span.clone(),
                    sym::Type::Primitive(sym::PrimitiveType::I64),
                )
            }
            ast::Expr::Tuple(_, values, _) => {
                let values = values
                    .iter()
                    .map(|v| self.gen_expr(v))
                    .collect::<Result<Vec<_>, _>>()?;

                let ty = sym::Type::Tuple(values.iter().map(|v| v.ty().clone()).collect());
                let expr = ir::ExprKind::Tuple(values);
                let expr = ir::Expr::new(expr, span.clone(), ty);
                expr
            }
            _ => todo!(),
        };
        Ok(expr)
    }
}
