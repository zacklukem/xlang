//! Handles generation of the IR

use crate::ast;
use crate::error_context::ErrorContext;
use crate::intern::Int;
use crate::ir;
use crate::mod_gen::{ModGenError, TypeGenerator};
use crate::ty;
use std::collections::{HashMap, VecDeque};
use std::iter::Iterator;

pub fn gen_fun_block<'ast, 'ty>(
    module: &ir::Module<'ty>,
    db_name: String,
    err: &mut ErrorContext,
    def_id: ir::DefId,
    params: Vec<(String, ty::Ty<'ty>)>,
    return_type: ty::Ty<'ty>,
    fun: &'ast ast::SpanBox<ast::FunBlock>,
    current_generics: Vec<String>,
) -> Result<ir::Fun<'ty>, ModGenError> {
    let (block, variable_defs) = {
        let mut ir_gen = IrGen {
            var_id: 0,
            module,
            err,
            params: params.iter().map(Clone::clone).collect(),
            scope: Box::new(Scope::from_params(params)),
            variable_defs: HashMap::new(),
            continue_break_label: Default::default(),
            label_next: None,
            return_type,
            current_generics,
        };
        let body = ir_gen.gen_fun_block(fun)?;
        let variable_defs = ir_gen
            .variable_defs()
            .into_iter()
            .map(|(a, b)| (a.clone(), b.clone()))
            .collect();
        (body, variable_defs)
    };
    Ok(ir::Fun {
        db_name,
        def_id,
        block,
        variable_defs,
    })
}

#[derive(Debug, Default)]
struct Scope {
    parent: Option<Box<Scope>>,
    /// Maps <String: block-scoped var name> to <String: function-scoped var name>
    variables: HashMap<String, String>,
}

impl Scope {
    fn from_params(params: Vec<(String, ty::Ty<'_>)>) -> Self {
        Scope {
            parent: None,
            variables: params.into_iter().map(|(a, _)| (a.clone(), a)).collect(),
        }
    }

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

struct IrGen<'mg, 'ty> {
    var_id: u32,
    module: &'mg ir::Module<'ty>,
    err: &'mg mut ErrorContext,
    scope: Box<Scope>,
    /// types of variables (variable scoped)
    params: HashMap<String, ty::Ty<'ty>>,
    variable_defs: HashMap<String, ty::Ty<'ty>>,
    continue_break_label: Vec<String>,
    label_next: Option<String>,
    return_type: ty::Ty<'ty>,
    current_generics: Vec<String>,
}

fn continue_label(v: &String) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &String) -> String {
    format!("{}_break", v)
}

impl<'ast, 'mg, 'ty> TypeGenerator<'ast, 'ty> for IrGen<'mg, 'ty> {
    fn current_generics(&self) -> &Vec<String> {
        &self.current_generics
    }

    fn module(&self) -> &ir::Module<'ty> {
        &self.module
    }
}

impl<'mg, 'ty, 'ast> IrGen<'mg, 'ty> {
    fn variable_defs(self) -> HashMap<String, ty::Ty<'ty>> {
        self.variable_defs
    }

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

    fn declare_var(&mut self, block_scope_name: &String, ty: ty::Ty<'ty>) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", block_scope_name, id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        self.scope
            .insert(block_scope_name.clone(), fun_scope_name.clone());
        fun_scope_name
    }

    fn declare_hidden_var(&mut self, ty: ty::Ty<'ty>) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", "hidden", id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        fun_scope_name
    }

    fn label_next(&mut self, label: String) {
        assert!(self.label_next.is_none());
        self.label_next = Some(label);
    }

    fn replace_generics(
        &self,
        ty: ty::Ty<'ty>,
        generics: &Vec<(String, ty::Ty<'ty>)>,
    ) -> ty::Ty<'ty> {
        crate::generics::replace_generics(self.module.ty_ctx(), ty, generics)
    }

    /// Returns the type of the name and a boolean which is true if the name islocal scoped and false if it is global scoped
    fn resolve_value(
        &self,
        name: &ir::Path,
        generics: &Vec<ty::Ty<'ty>>,
    ) -> Option<(ty::Ty<'ty>, Option<String>)> {
        if let ir::Path::Terminal(id) = name {
            if let Some(var) = self.scope.resolve(&id) {
                return self
                    .variable_defs
                    .get(var)
                    .cloned()
                    .or_else(|| self.params.get(var).cloned())
                    .map(|v| (v, Some(var.clone())));
            }
        }
        match self.module.get_def_by_path(name) {
            Some(ir::Def {
                kind:
                    ir::DefKind::Fun {
                        ty_params,
                        params,
                        return_type,
                        ..
                    },
                ..
            }) => {
                assert_eq!(ty_params.len(), generics.len());
                let params = params.iter().map(|(_, t)| *t).collect();
                // TODO: resolve t-params
                Some((
                    self.replace_generics(
                        self.module
                            .ty_ctx()
                            .int(ty::TyKind::Fun(params, *return_type)),
                        &Iterator::zip(ty_params.iter(), generics.iter())
                            .map(|(a, b)| (a.clone(), b.clone()))
                            .collect(),
                    ),
                    None,
                ))
            }
            _ => None,
        }
    }

    fn gen_fun_block(
        &mut self,
        body: &'ast ast::SpanBox<ast::FunBlock>,
    ) -> Result<ir::Stmt<'ty>, ModGenError> {
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
        body: &'ast ast::SpanVec<ast::Stmt>,
        close_brace: &ast::Span,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
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
        condition: &'ast ast::Spanned<ast::Expr>,
        block: &'ast ast::Spanned<ast::Stmt>,
        else_block: Option<&'ast ast::SpanBox<ast::Stmt>>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
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
        span: &'ast ast::Span,
        label: Option<&'ast ast::Ident>,
        condition: &'ast ast::Spanned<ast::Expr>,
        block: &'ast ast::Spanned<ast::Stmt>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
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
        label: Option<&'ast ast::Ident>,
        block: &'ast ast::Spanned<ast::Stmt>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
        let label_prefix = label
            .map(|v| v.str().into())
            .unwrap_or_else(|| format!("loop_{}", self.get_var_id()));

        self.continue_break_label.push(label_prefix.clone());

        let bool_ty = ty::bool_ty(self.module.ty_ctx());

        let condition = Box::new(ir::Expr::new(
            ir::ExprKind::Bool(true),
            span.clone(),
            bool_ty,
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
        out: &mut Vec<ir::StmtKind<'ty>>,
        span: &ast::Span,
        pattern: &'ast ast::Spanned<ast::Pattern>,
        ty: ty::Ty<'ty>,
        expr: ir::Expr<'ty>,
    ) -> Result<(), ModGenError> {
        match pattern.value() {
            ast::Pattern::Tuple(_, patterns, _) => {
                let global_var_name = self.declare_hidden_var(ty.clone());
                let lhs_expr = ir::ExprKind::Ident(global_var_name.clone());
                let lhs_expr = ir::Expr::new(lhs_expr, span.clone(), ty.clone())
                    .lhs_expr(self.module.ty_ctx());
                let assign_expr = ir::Expr::new(
                    ir::ExprKind::Assign(Box::new(lhs_expr), ir::AssignOp::Eq, Box::new(expr)),
                    span.clone(),
                    ty.clone(),
                );
                out.push(ir::StmtKind::Expr(Box::new(assign_expr)));

                if let ty::Ty(Int(ty::TyKind::Tuple(tys))) = &ty {
                    if tys.len() != patterns.len() {
                        self.err.err("Incompatible pattern types".into(), span);
                    }
                    for (i, (pattern, pat_ty)) in patterns.iter().zip(tys.iter()).enumerate() {
                        let access_expr = ir::ExprKind::Ident(global_var_name.clone());
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
                let expr = self.coerce(
                    expr,
                    ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::I32),
                )?;
                let ty = expr.ty();
                let global_var_name = self.declare_var(&id.str().into(), ty.clone());
                let lhs_expr = ir::ExprKind::Ident(global_var_name);
                let lhs_expr = ir::Expr::new(lhs_expr, id.span.clone(), ty.clone())
                    .lhs_expr(self.module.ty_ctx());
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
        span: &'ast ast::Span,
        pattern: &'ast ast::Spanned<ast::Pattern>,
        ty: Option<&'ast ast::SpanBox<ast::Type>>,
        expr: &'ast ast::Spanned<ast::Expr>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
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
        let ty = if let Some(_ty) = ty {
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
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
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

    fn gen_return(
        &mut self,
        span: &ast::Span,
        expr: Option<&ast::SpanBox<ast::Expr>>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
        let expr = expr
            .map(|e| self.gen_expr_coerce(e, self.return_type))
            .transpose()?;
        let ty = match &expr {
            Some(e) => e.ty().clone(),
            None => ty::void_ty(self.module.ty_ctx()),
        };
        if ty != self.return_type {
            self.err.err(
                format!(
                    "Invalid return type got: {} expected: {}",
                    ty, self.return_type
                ),
                span,
            );
        }
        Ok(ir::StmtKind::Return(expr.map(Box::new)))
    }

    fn gen_stmt(
        &mut self,
        stmt: &'ast ast::Spanned<ast::Stmt>,
    ) -> Result<ir::Stmt<'ty>, ModGenError> {
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
                label: _,
                initializer: _,
                range: _,
                block: _,
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
            ast::Stmt::Return(span, expr) => self.gen_return(span, expr.as_ref())?,
            ast::Stmt::Continue(span, label) => {
                self.gen_break_continue(false, span, label.as_ref())?
            }
            ast::Stmt::Break(span, label) => self.gen_break_continue(true, span, label.as_ref())?,

            ast::Stmt::Expr(expr) => ir::StmtKind::Expr(Box::new(self.gen_expr(expr)?)),
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

    fn gen_ident_expr(
        &mut self,
        span: &ast::Span,
        name: &'ast ast::Name,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let (name, generics) = self.gen_path_and_generics(name)?;
        let ty = self.resolve_value(&name, &generics);
        if ty.is_none() {
            self.err
                .err(format!("Name `{}` not found in scope", span.str()), span);
        }
        let (ty, var_name) = ty.unwrap_or_else(|| (ty::err_ty(self.module.ty_ctx()), None));
        let expr = if let Some(var) = var_name {
            // self.scope.resolve(&id)
            ir::ExprKind::Ident(var)
        } else {
            ir::ExprKind::GlobalIdent(name, generics)
        };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_integer_expr(
        &mut self,
        span: &ast::Span,
        _spec: &ast::IntegerSpecifier,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        // TODO(): Integer types
        let st = span.str();

        let kind = if st.contains('-') {
            ir::IntegerSpecifier::Signed(str::parse::<isize>(span.str()).unwrap())
        } else {
            ir::IntegerSpecifier::Unsigned(str::parse::<usize>(span.str()).unwrap())
        };

        let kind = ir::ExprKind::Integer(kind);
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::Integer),
        );
        Ok(expr)
    }

    fn gen_float_expr(
        &mut self,
        span: &ast::Span,
        _spec: &ast::FloatSpecifier,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        // TODO(): Float types
        let value = str::parse::<f64>(span.str()).unwrap();
        let kind = ir::ExprKind::Float(ir::FloatSpecifier::F64(value));
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::F64),
        );
        Ok(expr)
    }

    fn gen_string_expr(&mut self, span: &ast::Span) -> Result<ir::Expr<'ty>, ModGenError> {
        let value = span.str().into();
        let kind = ir::ExprKind::String(value);
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::U8)
                .slice_ty(self.module.ty_ctx())
                .ptr(self.module.ty_ctx()),
        );
        Ok(expr)
    }

    fn gen_bool_expr(
        &mut self,
        span: &ast::Span,
        value: bool,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let kind = ir::ExprKind::Bool(value);
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::Bool),
        );
        Ok(expr)
    }

    fn gen_expr_iter<T>(&mut self, iter: T) -> Result<Vec<ir::Expr<'ty>>, ModGenError>
    where
        T: Iterator<Item = &'ast ast::Spanned<ast::Expr>>,
    {
        let size_hint = iter.size_hint().0;
        let mut out = Vec::with_capacity(size_hint);
        for value in iter {
            out.push(self.gen_expr(value)?);
        }
        Ok(out)
    }

    fn gen_tuple_expr(
        &mut self,
        span: &ast::Span,
        values: &'ast ast::SpanVec<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let values = self.gen_expr_iter(values.iter())?;

        let ty = self
            .module
            .ty_ctx()
            .int(ty::TyKind::Tuple(values.iter().map(|v| v.ty()).collect()));
        let expr = ir::ExprKind::Tuple(values);
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_assign_expr(
        &mut self,
        span: &ast::Span,
        lhs: &ast::Spanned<ast::Expr>,
        op: &ast::Spanned<ast::AssignOp>,
        rhs: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let lhs = self.gen_expr(lhs)?;
        let lhs_ty = lhs.ty().clone();
        let lhs = lhs.lhs_expr(self.module.ty_ctx());
        let op = op.value().into();
        let rhs = self.gen_expr_coerce(rhs, lhs_ty)?;

        let ty = if lhs_ty != rhs.ty() {
            self.err.err(
                format!("Incompatible types {} and {}", lhs_ty, rhs.ty()),
                span,
            );
            ty::err_ty(self.module.ty_ctx())
        } else {
            lhs_ty
        };

        let expr = ir::ExprKind::Assign(Box::new(lhs), op, Box::new(rhs));
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_binary_expr(
        &mut self,
        span: &ast::Span,
        lhs: &ast::Spanned<ast::Expr>,
        op: &ast::Spanned<ast::BinOp>,
        rhs: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let lhs = self.gen_expr(lhs)?;
        let op = op.value().into();
        let rhs = self.gen_expr(rhs)?;

        let (lhs, rhs) = match (lhs.ty(), rhs.ty()) {
            (ty::Ty(Int(ty::TyKind::Pointer(_, _))), ty::Ty(Int(ty::TyKind::Pointer(_, _)))) => {
                let ty = ty::void_ty(self.module.ty_ctx()).ptr(self.module.ty_ctx());
                (self.coerce(lhs, ty)?, self.coerce(rhs, ty)?)
            }
            (
                ty::Ty(Int(ty::TyKind::Primitive(lhs_ty))),
                ty::Ty(Int(ty::TyKind::Primitive(rhs_ty))),
            ) => {
                let ty = lhs_ty.min(rhs_ty).clone();
                let ty = self.module.ty_ctx().int(ty::TyKind::Primitive(ty));
                (self.coerce(lhs, ty)?, self.coerce(rhs, ty)?)
            }
            _ => (lhs, rhs),
        };

        if lhs.ty() != rhs.ty() {
            self.err.err(
                format!("Incompatible types {} <> {}", lhs.ty(), rhs.ty()),
                span,
            );
        }

        let ty = match op {
            ir::BinOp::AndAnd | ir::BinOp::OrOr => {
                if let ty::Ty(Int(ty::TyKind::Primitive(ty::PrimitiveType::Bool))) = lhs.ty() {
                    lhs.ty()
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.module.ty_ctx())
                }
            }
            ir::BinOp::Lt
            | ir::BinOp::Gt
            | ir::BinOp::LtEq
            | ir::BinOp::GtEq
            | ir::BinOp::EqEq
            | ir::BinOp::NotEq
                if lhs.ty().is_numeric()
                    || matches!(lhs.ty(), ty::Ty(Int(ty::TyKind::Pointer(_, _)))) =>
            {
                ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::Bool)
            }
            _ if !lhs.ty().is_numeric() => {
                self.err.err("Incompatible types".into(), span);
                ty::err_ty(self.module.ty_ctx())
            }
            _ => lhs.ty().clone(),
        };

        let expr = ir::ExprKind::Binary(Box::new(lhs), op, Box::new(rhs));
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_unary_expr(
        &mut self,
        span: &ast::Span,
        op: &ast::Spanned<ast::UnaryOp>,
        rhs: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let op = op.value().into();
        let rhs = self.gen_expr(rhs)?;

        let ty = match op {
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot if rhs.ty().is_numeric() => rhs.ty().clone(),
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot => {
                self.err.err("Incompatible types".into(), span);
                ty::err_ty(self.module.ty_ctx())
            }
            ir::UnaryOp::LogNot => {
                if let ty::Ty(Int(ty::TyKind::Primitive(ty::PrimitiveType::Bool))) = rhs.ty() {
                    rhs.ty()
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.module.ty_ctx())
                }
            }

            ir::UnaryOp::Deref => {
                if let ty::Ty(Int(ty::TyKind::Pointer(_mutable, ty))) = rhs.ty() {
                    *ty
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.module.ty_ctx())
                }
            }

            ir::UnaryOp::Ref => rhs.ty().ptr(self.module.ty_ctx()),

            ir::UnaryOp::RefMut => rhs.ty().ptr(self.module.ty_ctx()),

            ir::UnaryOp::Box => rhs.ty().ptr(self.module.ty_ctx()),
        };

        let expr = ir::ExprKind::Unary(op, Box::new(rhs));
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_dot_expr(
        &mut self,
        span: &ast::Span,
        lhs: &ast::Spanned<ast::Expr>,
        rhs: &ast::Ident,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let mut lhs = self.gen_expr(lhs)?;
        let rhs: String = rhs.str().into();

        // Dereferencing
        while let ty::Ty(Int(ty::TyKind::Pointer(_mutable, ty))) = lhs.ty().clone() {
            lhs = ir::Expr::new(
                ir::ExprKind::Unary(ir::UnaryOp::Deref, Box::new(lhs)),
                span.clone(),
                *ty,
            );
        }

        let ty = match lhs.ty().0 .0 {
            ty::TyKind::Struct(ty::StructType {
                def_id,
                ty_params: instance_ty_params,
                ..
            }) => {
                let def = self.module.get_def_by_id(*def_id);
                if let ir::Def {
                    kind:
                        ir::DefKind::Struct {
                            members,
                            symbols,
                            ty_params: struct_ty_params,
                        },
                    ..
                } = def
                {
                    assert_eq!(instance_ty_params.len(), struct_ty_params.len());
                    if let Some(def_id) = symbols.get(&rhs) {
                        let def = self.module.get_def_by_id(*def_id);
                        match &def.kind {
                            ir::DefKind::Fun {
                                params,
                                return_type,
                                ty_params: fun_ty_params,
                                ..
                            } => {
                                // let self_type = match params.first() {
                                //     Some((name, ty)) if name == "self" => ty,
                                //     _ => todo!("err: func must have self"),
                                // };
                                // TODO: match self params to body

                                assert_eq!(instance_ty_params.len(), fun_ty_params.len());

                                let typ_iter =
                                    Iterator::zip(fun_ty_params.iter(), instance_ty_params.iter())
                                        .map(|(a, b)| (a.clone(), b.clone()))
                                        .collect();

                                let params = params
                                    .iter()
                                    .map(|(_, t)| self.replace_generics(*t, &typ_iter))
                                    .collect();

                                let return_type = self.replace_generics(*return_type, &typ_iter);

                                let ty = self
                                    .module
                                    .ty_ctx()
                                    .int(ty::TyKind::Fun(params, return_type));

                                let pass_ty_ref = lhs.ty().ptr(self.module.ty_ctx());

                                let pass_expr =
                                    ir::ExprKind::Unary(ir::UnaryOp::Ref, Box::new(lhs));
                                let pass_expr = ir::Expr::new(pass_expr, span.clone(), pass_ty_ref);

                                // Struct::method
                                let path = self.module.get_path_by_def_id(*def_id);
                                let expr = ir::ExprKind::GlobalIdent(
                                    path.clone(),
                                    instance_ty_params.clone(),
                                );
                                let expr =
                                    ir::Expr::new_pass(expr, span.clone(), ty, Box::new(pass_expr));
                                return Ok(expr);
                            }
                            _ => todo!("error"),
                        }
                    } else if let Some(ty) = members.get(&rhs) {
                        let generics =
                            Iterator::zip(struct_ty_params.iter(), instance_ty_params.iter())
                                .map(|(a, b)| (a.clone(), *b))
                                .collect();
                        self.replace_generics(*ty, &generics)
                    } else {
                        self.err.err("Field not found in struct".into(), span);
                        ty::err_ty(self.module.ty_ctx())
                    }
                } else {
                    self.err
                        .err("The dot operator can only be used on a struct".into(), span);
                    ty::err_ty(self.module.ty_ctx())
                }
            }
            _ => {
                self.err
                    .err("The dot operator can only be used on a struct".into(), span);
                ty::err_ty(self.module.ty_ctx())
            }
        };

        let expr = ir::ExprKind::Dot(Box::new(lhs), rhs);
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_cast_expr(
        &mut self,
        span: &ast::Span,
        expr: &ast::Spanned<ast::Expr>,
        ty: &ast::Spanned<ast::Type>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let expr = self.gen_expr(expr)?;
        let ty = self.gen_type(ty)?;

        let ty = match (expr.ty().0 .0, ty.0 .0) {
            (
                ty::TyKind::Primitive(ty::PrimitiveType::Void),
                ty::TyKind::Primitive(ty::PrimitiveType::Void),
            ) => {
                self.err.err("Cannot cast void".into(), span);
                ty::err_ty(self.module.ty_ctx())
            }
            (
                ty::TyKind::Primitive(ty::PrimitiveType::Bool),
                ty::TyKind::Primitive(ty::PrimitiveType::Bool),
            ) => {
                self.err.err("Cannot cast bool".into(), span);
                ty::err_ty(self.module.ty_ctx())
            }
            _ => ty,
        };

        let expr = ir::ExprKind::Cast(Box::new(expr), ty);
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_ternary_expr(
        &mut self,
        span: &ast::Span,
        condition: &ast::Spanned<ast::Expr>,
        then_expr: &ast::Spanned<ast::Expr>,
        else_expr: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let condition = self.gen_expr(condition)?;
        let then_expr = self.gen_expr(then_expr)?;
        let else_expr = self.gen_expr_coerce(else_expr, then_expr.ty())?;

        match condition.ty().0 .0 {
            ty::TyKind::Primitive(ty::PrimitiveType::Bool) => (),
            _ => {
                self.err.err(
                    "If statement condition must be bool type".into(),
                    condition.span(),
                );
            }
        }

        let ty = if then_expr.ty() == else_expr.ty() {
            then_expr.ty().clone()
        } else {
            self.err.err(
                "If and else value types don't match".into(),
                then_expr.span(),
            );
            ty::err_ty(self.module.ty_ctx())
        };

        let condition = Box::new(condition);
        let then_expr = Box::new(then_expr);
        let else_expr = Box::new(else_expr);

        let expr = ir::ExprKind::Ternary {
            condition,
            then_expr,
            else_expr,
        };

        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_range_expr(
        &mut self,
        span: &ast::Span,
        range: &ast::Range,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        macro_rules! zero {
            () => {
                ir::Expr::new(
                    ir::ExprKind::Integer(ir::IntegerSpecifier::USize(0)),
                    span.clone(),
                    ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::USize),
                )
            };
        }
        macro_rules! check_type {
            ($e: expr) => {
                if let ty::TyKind::Primitive(ty::PrimitiveType::USize) = $e.0.0 {
                    ()
                } else {
                    self.err.err("Range values must be usize".into(), span);
                }
            };
        }
        let expr = match range {
            ast::Range::All(_) => ir::ExprKind::RangeFrom(Box::new(zero!())),
            ast::Range::Full(lhs, _, rhs) => {
                let lhs = self.gen_expr(lhs.as_ref())?;
                let rhs = self.gen_expr(rhs.as_ref())?;
                check_type!(lhs.ty());
                check_type!(rhs.ty());
                ir::ExprKind::Range(Box::new(lhs), Box::new(rhs))
            }
            ast::Range::Start(lhs, _) => {
                let lhs = self.gen_expr(lhs.as_ref())?;
                check_type!(lhs.ty());
                ir::ExprKind::RangeFrom(Box::new(lhs))
            }
            ast::Range::End(_, rhs) => {
                let rhs = self.gen_expr(rhs.as_ref())?;
                check_type!(rhs.ty());
                ir::ExprKind::Range(Box::new(zero!()), Box::new(rhs))
            }
        };

        let expr = ir::Expr::new(expr, span.clone(), ty::range_ty(self.module.ty_ctx()));
        Ok(expr)
    }

    fn gen_call_expr(
        &mut self,
        span: &ast::Span,
        expr: &ast::Spanned<ast::Expr>,
        arguments: &ast::SpanVec<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let mut expr = self.gen_expr(expr)?;

        let fun_pass = std::mem::take(expr.fun_pass_mut());

        let (params, return_type) = match expr.ty().0 .0 {
            ty::TyKind::Fun(params, return_type) => (params, return_type),
            _ => {
                self.err.err("Expected function type".into(), span);
                return Ok(ir::Expr::new(
                    ir::ExprKind::Err,
                    span.clone(),
                    ty::err_ty(self.module.ty_ctx()),
                ));
            }
        };

        let mut arguments = {
            let mut params_iter = params.iter();

            // Skip first if self
            if fun_pass.is_some() {
                params_iter.next();
            }

            let mut out = VecDeque::with_capacity(arguments.len() + 1);
            for (e, ty) in arguments.iter().zip(params_iter) {
                out.push_back(self.gen_expr_coerce(e, *ty)?)
            }
            out
        };

        if let Some(fun_pass) = fun_pass {
            arguments.push_front(*fun_pass);
        }

        let arguments: Vec<_> = arguments.into();

        let ty = if params.len() != arguments.len() {
            self.err.err("Invalid number of arguments".into(), span);
            ty::err_ty(self.module.ty_ctx())
        } else {
            for (p_ty, ir::Expr { ty, span, .. }) in params.iter().zip(arguments.iter()) {
                if p_ty != ty {
                    self.err
                        .err(format!("Invalid argument type {} {}", p_ty, ty), span);
                }
            }
            *return_type
        };

        let expr = Box::new(expr);

        let expr = ir::ExprKind::Call { expr, arguments };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_index_expr(
        &mut self,
        span: &ast::Span,
        expr: &ast::Spanned<ast::Expr>,
        index: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let expr = self.gen_expr(expr)?;
        let index = self.gen_expr_coerce(
            index,
            ty::primitive_ty(self.module.ty_ctx(), ty::PrimitiveType::USize),
        )?;

        let ty = match (expr.ty().0 .0, index.ty().0 .0) {
            (
                ty::TyKind::Pointer(_, inner_type),
                ty::TyKind::Primitive(ty::PrimitiveType::USize),
            ) => *inner_type,
            _ => ty::err_ty(self.module.ty_ctx()),
        };

        let expr = Box::new(expr);
        let index = Box::new(index);

        let expr = ir::ExprKind::Index { expr, index };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_array_expr(
        &mut self,
        span: &ast::Span,
        members: &ast::SpanVec<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let members = self.gen_expr_iter(members.iter())?;

        let ty = if !members.is_empty() {
            let first = members.first().unwrap();
            for member in members.iter().skip(1) {
                if member.ty() != first.ty() {
                    self.err
                        .err("Array values must be homogeneous".into(), member.span());
                    break; // only emit one err
                }
            }
            first.ty()
        } else {
            ty::ukn_ty(self.module.ty_ctx())
        };

        let ty = self
            .module
            .ty_ctx()
            .int(ty::TyKind::SizedArray(members.len(), ty));

        let expr = ir::ExprKind::Array { members };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_struct_expr(
        &mut self,
        span: &ast::Span,
        type_name: &ast::Spanned<ast::Name>,
        members: &ast::SpanVec<(ast::Ident, ast::SpanBox<ast::Expr>)>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let type_name_span = type_name.span.clone();
        let (type_name, type_generics) = self.gen_path_and_generics(type_name.value())?;
        let mut members: Vec<(String, _)> = members
            .iter()
            .map(|ast::Spanned { value: (id, v), .. }| {
                Ok((id.str().into(), Box::new(self.gen_expr(v)?)))
            })
            .collect::<Result<Vec<_>, ModGenError>>()?;

        let ty = if let Some(ir::Def {
            kind:
                ir::DefKind::Struct {
                    members: struct_members,
                    ..
                },
            ..
        }) = self.module.get_def_by_path(&type_name)
        {
            let def_id = self.module.get_def_id_by_path(&type_name).unwrap();
            if struct_members.len() != members.len() {
                self.err
                    .err("Missing or extra struct fields".into(), &type_name_span);
                ty::err_ty(self.module.ty_ctx())
            } else {
                let mut failed = false;
                for (name, expr) in &mut members {
                    match struct_members.get(name) {
                        Some(member) => {
                            {
                                let expr_ref = expr.as_mut();
                                // Hax
                                let expr = std::mem::replace(
                                    expr_ref,
                                    ir::Expr::new(
                                        ir::ExprKind::Err,
                                        ast::Span::dummy(),
                                        ty::err_ty(self.module.ty_ctx()),
                                    ),
                                );
                                *expr_ref = self.coerce(expr, *member)?;
                            }
                            if expr.ty() != *member {
                                self.err.err("Invalid type".into(), expr.span());
                                failed = true;
                            }
                        }
                        None => {
                            self.err.err("Field doesn't exist".into(), expr.span());
                            failed = true;
                        }
                    };
                }
                if failed {
                    ty::err_ty(self.module.ty_ctx())
                } else {
                    self.module.ty_ctx().int(ty::TyKind::Struct(ty::StructType {
                        def_id,
                        path: type_name,
                        ty_params: type_generics,
                    }))
                }
            }
        } else {
            self.err.err("Invalid struct name".into(), &type_name_span);
            ty::err_ty(self.module.ty_ctx())
        };
        let expr = ir::ExprKind::Struct { ty, members };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_expr_coerce(
        &mut self,
        expr: &ast::Spanned<ast::Expr>,
        ty: ty::Ty<'ty>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let expr = self.gen_expr(expr)?;
        self.coerce(expr, ty)
    }

    fn coerce(
        &mut self,
        expr: ir::Expr<'ty>,
        ty: ty::Ty<'ty>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let expr_span = expr.span().clone();
        match (ty.0 .0, expr.ty().0 .0) {
            (ty::TyKind::Pointer(ptr_kind, inner_ty), ty::TyKind::Pointer(_, _))
                if matches!(expr.kind(), ir::ExprKind::Null) =>
            {
                let ty = self
                    .module
                    .ty_ctx()
                    .int(ty::TyKind::Pointer(ptr_kind.clone(), inner_ty.clone()));
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = ir::Expr::new(expr, expr_span, ty);
                Ok(expr)
            }
            (ty::TyKind::Pointer(ptr_kind, inner_ty), ty::TyKind::Pointer(_, _))
                if matches!(
                    inner_ty.0 .0,
                    ty::TyKind::Primitive(ty::PrimitiveType::Void)
                ) =>
            {
                let ty = self
                    .module
                    .ty_ctx()
                    .int(ty::TyKind::Pointer(ptr_kind.clone(), inner_ty.clone()));
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = ir::Expr::new(expr, expr_span, ty);
                Ok(expr)
            }
            (ty::TyKind::Primitive(target), ty::TyKind::Primitive(current))
                if current.is_integral() && target.is_integral() && target < current =>
            {
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = ir::Expr::new(expr, expr_span, ty);
                Ok(expr)
            }
            _ => Ok(expr),
        }
    }

    fn gen_expr(&mut self, expr: &ast::Spanned<ast::Expr>) -> Result<ir::Expr<'ty>, ModGenError> {
        let expr_span = &expr.span;
        let expr = match expr.value() {
            ast::Expr::Ident(name) => self.gen_ident_expr(expr_span, name)?,
            ast::Expr::Integer(span, spec) => self.gen_integer_expr(span, spec)?,
            ast::Expr::Float(span, spec) => self.gen_float_expr(span, spec)?,
            ast::Expr::String(span) => self.gen_string_expr(span)?,
            ast::Expr::Bool(span, value) => self.gen_bool_expr(span, *value)?,

            ast::Expr::Tuple(_, values, _) => self.gen_tuple_expr(expr_span, values)?,

            ast::Expr::Assign(lhs, op, rhs) => {
                self.gen_assign_expr(expr_span, lhs.as_ref(), op, rhs.as_ref())?
            }
            ast::Expr::Binary(lhs, op, rhs) => {
                self.gen_binary_expr(expr_span, lhs.as_ref(), op, rhs.as_ref())?
            }

            ast::Expr::Unary(op, rhs) => self.gen_unary_expr(expr_span, op, rhs.as_ref())?,

            ast::Expr::Dot(lhs, _, rhs) => self.gen_dot_expr(expr_span, lhs.as_ref(), rhs)?,

            ast::Expr::Cast(lhs, _, rhs) => {
                self.gen_cast_expr(expr_span, lhs.as_ref(), rhs.as_ref())?
            }

            ast::Expr::Range(range) => self.gen_range_expr(expr_span, range)?,

            ast::Expr::Ternary {
                condition,
                then_expr,
                else_expr,
                ..
            } => self.gen_ternary_expr(expr_span, condition, then_expr, else_expr)?,

            // ternary
            ast::Expr::Call {
                expr, arguments, ..
            } => self.gen_call_expr(expr_span, expr.as_ref(), arguments)?,

            ast::Expr::Index { expr, index, .. } => {
                self.gen_index_expr(expr_span, expr.as_ref(), index.as_ref())?
            }
            ast::Expr::Array { members, .. } => self.gen_array_expr(expr_span, members)?,
            ast::Expr::Struct {
                type_name, members, ..
            } => self.gen_struct_expr(expr_span, type_name, members)?,
            ast::Expr::Null(_) => ir::Expr::new(
                ir::ExprKind::Null,
                expr_span.clone(),
                ty::void_ty(self.module.ty_ctx()).ptr(self.module.ty_ctx()),
            ),
        };
        Ok(expr)
    }
}
