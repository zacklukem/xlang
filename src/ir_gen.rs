use crate::ast;
use crate::error_context::ErrorContext;
use crate::ir;
use crate::mod_gen::ModGenError;
use crate::symbol as sym;
use std::collections::{HashMap, VecDeque};

pub fn gen_fun_block<'mg>(
    module: &'mg ir::Module,
    err: &'mg mut ErrorContext,
    name: &sym::Name,
    params: &Vec<(String, sym::Type)>,
    return_type: &sym::Type,
    fun: &ast::SpanBox<ast::FunBlock>,
) -> Result<ir::Fun, ModGenError> {
    let mut variable_defs = HashMap::new();
    let mut ir_gen = IrGen {
        var_id: 0,
        module,
        err,
        params: params.iter().map(Clone::clone).collect(),
        scope: Box::new(Scope::from_params(params)),
        variable_defs: &mut variable_defs,
        continue_break_label: Default::default(),
        label_next: None,
        return_type: return_type,
    };
    let body = ir_gen.gen_fun_block(fun)?;
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
    fn from_params(params: &Vec<(String, sym::Type)>) -> Self {
        Scope {
            parent: None,
            variables: params.iter().map(|(a, _)| (a.clone(), a.clone())).collect(),
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

struct IrGen<'a, 'mg> {
    var_id: u32,
    module: &'mg ir::Module,
    err: &'mg mut ErrorContext,
    scope: Box<Scope>,
    /// types of variables (variable scoped)
    params: HashMap<String, sym::Type>,
    variable_defs: &'a mut HashMap<String, sym::Type>,
    continue_break_label: Vec<String>,
    label_next: Option<String>,
    return_type: &'a sym::Type,
}

fn continue_label(v: &String) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &String) -> String {
    format!("{}_break", v)
}

impl<'a, 'mg> IrGen<'a, 'mg> {
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
        if let ast::Name::Ident(ast::Ident { span }, _) = name {
            let id = span.str().into();
            if let Some(var) = self.scope.resolve(&id) {
                return if let Some(t) = self.variable_defs.get(var) {
                    Some(t.clone())
                } else if let Some(t) = self.params.get(var) {
                    Some(t.clone())
                } else {
                    None
                };
            }
        }
        let name = sym::Name::from_ast_name(name, self.module.const_eval());
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
                        types,
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
        body: &ast::SpanBox<ast::FunBlock>,
    ) -> Result<ir::Stmt, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<(), ModGenError> {
        match pattern.value() {
            ast::Pattern::Tuple(_, patterns, _) => {
                let global_var_name = self.declare_hidden_var(ty.clone());
                let lhs_expr =
                    ir::ExprKind::Ident(sym::Name::Ident(global_var_name.clone(), Vec::new()));
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
                        let access_expr = ir::ExprKind::Ident(sym::Name::Ident(
                            global_var_name.clone(),
                            Vec::new(),
                        ));
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
                let expr = self.coerce(expr, &sym::Type::Primitive(sym::PrimitiveType::I32))?;
                let ty = expr.ty().clone();
                let global_var_name = self.declare_var(&id.str().into(), ty.clone());
                let lhs_expr = ir::ExprKind::Ident(sym::Name::Ident(global_var_name, Vec::new()));
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
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
    ) -> Result<ir::StmtKind, ModGenError> {
        let expr = expr
            .map(|e| self.gen_expr_coerce(e, self.return_type))
            .transpose()?;
        let ty = match &expr {
            Some(e) => e.ty().clone(),
            None => sym::Type::Primitive(sym::PrimitiveType::Void),
        };
        if ty != *self.return_type {
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

    fn gen_stmt(&mut self, stmt: &ast::Spanned<ast::Stmt>) -> Result<ir::Stmt, ModGenError> {
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
        name: &ast::Name,
    ) -> Result<ir::Expr, ModGenError> {
        let ty = self.resolve(name);
        if ty.is_none() {
            self.err
                .err(format!("Name `{}` not found in scope", span.str()), span);
        }
        let ty = ty.unwrap_or_else(|| sym::Type::Err);
        let expr = ir::ExprKind::Ident(sym::Name::from_ast_name(name, self.module.const_eval()));
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_integer_expr(
        &mut self,
        span: &ast::Span,
        _spec: &ast::IntegerSpecifier,
    ) -> Result<ir::Expr, ModGenError> {
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
            sym::Type::Primitive(sym::PrimitiveType::Integer),
        );
        Ok(expr)
    }

    fn gen_float_expr(
        &mut self,
        span: &ast::Span,
        _spec: &ast::FloatSpecifier,
    ) -> Result<ir::Expr, ModGenError> {
        // TODO(): Float types
        let value = str::parse::<f64>(span.str()).unwrap();
        let kind = ir::ExprKind::Float(ir::FloatSpecifier::F64(value));
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            sym::Type::Primitive(sym::PrimitiveType::F64),
        );
        Ok(expr)
    }

    fn gen_string_expr(&mut self, span: &ast::Span) -> Result<ir::Expr, ModGenError> {
        let value = span.str().into();
        let kind = ir::ExprKind::String(value);
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            // String slice
            sym::Type::Pointer(
                sym::PointerType::Star,
                Box::new(sym::Type::UnsizedArray(Box::new(sym::Type::Primitive(
                    sym::PrimitiveType::U8,
                )))),
            ),
        );
        Ok(expr)
    }

    fn gen_bool_expr(&mut self, span: &ast::Span, value: bool) -> Result<ir::Expr, ModGenError> {
        let kind = ir::ExprKind::Bool(value);
        let expr = ir::Expr::new(
            kind,
            span.clone(),
            sym::Type::Primitive(sym::PrimitiveType::Bool),
        );
        Ok(expr)
    }

    fn gen_tuple_expr(
        &mut self,
        span: &ast::Span,
        values: &ast::SpanVec<ast::Expr>,
    ) -> Result<ir::Expr, ModGenError> {
        let values = values
            .iter()
            .map(|v| self.gen_expr(v))
            .collect::<Result<Vec<_>, _>>()?;

        let ty = sym::Type::Tuple(values.iter().map(|v| v.ty().clone()).collect());
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
    ) -> Result<ir::Expr, ModGenError> {
        let lhs = self.gen_expr(lhs)?;
        let lhs_ty = lhs.ty().clone();
        let lhs = lhs.lhs_expr();
        let op = op.value().into();
        let rhs = self.gen_expr_coerce(rhs, &lhs_ty)?;

        let ty = if lhs_ty != *rhs.ty() {
            self.err.err(
                format!("Incompatible types {} and {}", lhs_ty, rhs.ty()),
                span,
            );
            sym::Type::Err
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
    ) -> Result<ir::Expr, ModGenError> {
        let lhs = self.gen_expr(lhs)?;
        let op = op.value().into();
        let rhs = self.gen_expr(rhs)?;

        let (lhs, rhs) = match (lhs.ty(), rhs.ty()) {
            (sym::Type::Pointer(_, _), sym::Type::Pointer(_, _)) => {
                let ty = sym::Type::Pointer(
                    sym::PointerType::Star,
                    Box::new(sym::Type::Primitive(sym::PrimitiveType::Void)),
                );
                (self.coerce(lhs, &ty)?, self.coerce(rhs, &ty)?)
            }
            (sym::Type::Primitive(lhs_ty), sym::Type::Primitive(rhs_ty)) => {
                let ty = lhs_ty.min(rhs_ty).clone();
                let ty = sym::Type::Primitive(ty);
                (self.coerce(lhs, &ty)?, self.coerce(rhs, &ty)?)
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
                if let sym::Type::Primitive(sym::PrimitiveType::Bool) = lhs.ty() {
                    lhs.ty().clone()
                } else {
                    self.err.err("Incompatible types".into(), span);
                    sym::Type::Err
                }
            }
            ir::BinOp::Lt
            | ir::BinOp::Gt
            | ir::BinOp::LtEq
            | ir::BinOp::GtEq
            | ir::BinOp::EqEq
            | ir::BinOp::NotEq
                if lhs.ty().is_numeric() || matches!(lhs.ty(), sym::Type::Pointer(_, _)) =>
            {
                sym::Type::Primitive(sym::PrimitiveType::Bool)
            }
            _ if !lhs.ty().is_numeric() => {
                self.err.err("Incompatible types".into(), span);
                sym::Type::Err
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
    ) -> Result<ir::Expr, ModGenError> {
        let op = op.value().into();
        let rhs = self.gen_expr(rhs)?;

        let ty = match op {
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot if rhs.ty().is_numeric() => rhs.ty().clone(),
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot => {
                self.err.err("Incompatible types".into(), span);
                sym::Type::Err
            }
            ir::UnaryOp::LogNot => {
                if let sym::Type::Primitive(sym::PrimitiveType::Bool) = rhs.ty() {
                    rhs.ty().clone()
                } else {
                    self.err.err("Incompatible types".into(), span);
                    sym::Type::Err
                }
            }

            ir::UnaryOp::Deref => {
                if let sym::Type::Pointer(_mutable, ty) = rhs.ty() {
                    ty.as_ref().clone()
                } else {
                    self.err.err("Incompatible types".into(), span);
                    sym::Type::Err
                }
            }

            ir::UnaryOp::Ref => {
                sym::Type::Pointer(sym::PointerType::Star, Box::new(rhs.ty().clone()))
            }

            ir::UnaryOp::RefMut => {
                sym::Type::Pointer(sym::PointerType::StarMut, Box::new(rhs.ty().clone()))
            }

            ir::UnaryOp::Box => {
                sym::Type::Pointer(sym::PointerType::Star, Box::new(rhs.ty().clone()))
            }
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
    ) -> Result<ir::Expr, ModGenError> {
        let mut lhs = self.gen_expr(lhs)?;
        let rhs: String = rhs.str().into();

        while let sym::Type::Pointer(_mutable, ty) = lhs.ty().clone() {
            lhs = ir::Expr::new(
                ir::ExprKind::Unary(ir::UnaryOp::Deref, Box::new(lhs)),
                span.clone(),
                *ty,
            );
        }

        let ty = match lhs.ty() {
            sym::Type::Named(struct_name) => {
                let ty_sym = self.module.ty_ctx.root.resolve(struct_name);
                if let Some(sym::SymbolInfo {
                    symbol:
                        sym::Symbol::Struct {
                            members,
                            symbols,
                            types: struct_ty_params,
                        },
                    ..
                }) = ty_sym
                {
                    if let Some(sym::SymbolInfo {
                        symbol:
                            sym::Symbol::Fun {
                                params,
                                return_type,
                                types: fun_ty_params,
                            },
                        ..
                    }) = symbols.get(&rhs)
                    {
                        // The type is a method
                        let fun_name = sym::Name::with_end(
                            &struct_name,
                            sym::Name::Ident(rhs.clone(), Vec::new()),
                        );

                        // Type of method
                        let ty = sym::Type::Fun(
                            params.iter().map(|v| v.1.clone()).collect(),
                            return_type.clone(),
                        );

                        let pass_ty_ref = lhs.ty().ptr();

                        let pass_expr = ir::ExprKind::Unary(ir::UnaryOp::Ref, Box::new(lhs));
                        let pass_expr = ir::Expr::new(pass_expr, span.clone(), pass_ty_ref);

                        // Struct::method
                        let expr = ir::ExprKind::Ident(fun_name);
                        let expr = ir::Expr::new_pass(expr, span.clone(), ty, Box::new(pass_expr));
                        return Ok(expr);
                    } else if let Some(ty) = members.get(&rhs) {
                        ty.clone()
                    } else {
                        self.err.err("Field not found in struct".into(), span);
                        sym::Type::Err
                    }
                } else {
                    self.err
                        .err("The dot operator can only be used on a struct".into(), span);
                    sym::Type::Err
                }
            }
            _ => {
                self.err
                    .err("The dot operator can only be used on a struct".into(), span);
                sym::Type::Err
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
    ) -> Result<ir::Expr, ModGenError> {
        let expr = self.gen_expr(expr)?;
        let ty = sym::Type::from_ast_type(ty.value(), self.module.const_eval());

        let ty = match (expr.ty(), &ty) {
            (
                sym::Type::Primitive(sym::PrimitiveType::Void),
                sym::Type::Primitive(sym::PrimitiveType::Void),
            ) => {
                self.err.err("Cannot cast void".into(), span);
                sym::Type::Err
            }
            (
                sym::Type::Primitive(sym::PrimitiveType::Bool),
                sym::Type::Primitive(sym::PrimitiveType::Bool),
            ) => {
                self.err.err("Cannot cast bool".into(), span);
                sym::Type::Err
            }
            _ => ty,
        };

        let expr = ir::ExprKind::Cast(Box::new(expr), Box::new(ty.clone()));
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_ternary_expr(
        &mut self,
        span: &ast::Span,
        condition: &ast::Spanned<ast::Expr>,
        then_expr: &ast::Spanned<ast::Expr>,
        else_expr: &ast::Spanned<ast::Expr>,
    ) -> Result<ir::Expr, ModGenError> {
        let condition = self.gen_expr(condition)?;
        let then_expr = self.gen_expr(then_expr)?;
        let else_expr = self.gen_expr_coerce(else_expr, then_expr.ty())?;

        match condition.ty() {
            sym::Type::Primitive(sym::PrimitiveType::Bool) => (),
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
            sym::Type::Err
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
    ) -> Result<ir::Expr, ModGenError> {
        macro_rules! zero {
            () => {
                ir::Expr::new(
                    ir::ExprKind::Integer(ir::IntegerSpecifier::USize(0)),
                    span.clone(),
                    sym::Type::Primitive(sym::PrimitiveType::USize),
                )
            };
        }
        macro_rules! check_type {
            ($e: expr) => {
                if let sym::Type::Primitive(sym::PrimitiveType::USize) = $e {
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

        let expr = ir::Expr::new(
            expr,
            span.clone(),
            sym::Type::Range(Box::new(sym::Type::Primitive(sym::PrimitiveType::USize))),
        );
        Ok(expr)
    }

    fn gen_call_expr(
        &mut self,
        span: &ast::Span,
        expr: &ast::Spanned<ast::Expr>,
        arguments: &ast::SpanVec<ast::Expr>,
    ) -> Result<ir::Expr, ModGenError> {
        let mut expr = self.gen_expr(expr)?;

        let fun_pass = std::mem::take(expr.fun_pass_mut());

        let (params, return_type) = match expr.ty() {
            sym::Type::Fun(params, return_type) => (params, return_type),
            _ => {
                self.err.err("Expected function type".into(), span);
                return Ok(ir::Expr::new(
                    ir::ExprKind::Err,
                    span.clone(),
                    sym::Type::Err,
                ));
            }
        };

        let mut arguments = {
            let mut params_iter = params.iter();

            // Skip first if self
            if fun_pass.is_some() {
                params_iter.next();
            }

            arguments
                .iter()
                .zip(params_iter)
                .map(|(e, ty)| self.gen_expr_coerce(e, ty))
                .collect::<Result<VecDeque<_>, _>>()?
        };

        if let Some(fun_pass) = fun_pass {
            arguments.push_front(*fun_pass);
        }

        let arguments: Vec<_> = arguments.into();

        let ty = if params.len() != arguments.len() {
            self.err.err("Invalid number of arguments".into(), span);
            sym::Type::Err
        } else {
            for (p_ty, ir::Expr { ty, span, .. }) in params.iter().zip(arguments.iter()) {
                if p_ty != ty {
                    self.err
                        .err(format!("Invalid argument type {} {}", p_ty, ty), span);
                }
            }
            return_type.as_ref().clone()
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
    ) -> Result<ir::Expr, ModGenError> {
        let mut expr = self.gen_expr(expr)?;
        let index =
            self.gen_expr_coerce(index, &sym::Type::Primitive(sym::PrimitiveType::USize))?;

        while let sym::Type::Pointer(_mutable, ty) = expr.ty().clone() {
            expr = ir::Expr::new(
                ir::ExprKind::Unary(ir::UnaryOp::Deref, Box::new(expr)),
                span.clone(),
                *ty,
            );
        }

        let ty = match (expr.ty(), index.ty()) {
            (sym::Type::UnsizedArray(inner_ty), sym::Type::Range(v))
                if matches!(v.as_ref(), sym::Type::Primitive(sym::PrimitiveType::USize)) =>
            {
                sym::Type::UnsizedArray(inner_ty.clone())
            }
            (
                sym::Type::UnsizedArray(inner_ty) | sym::Type::SizedArray(_, inner_ty),
                sym::Type::Primitive(sym::PrimitiveType::USize),
            ) => inner_ty.as_ref().clone(),
            _ => sym::Type::Err,
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
    ) -> Result<ir::Expr, ModGenError> {
        let members = members
            .iter()
            .map(|v| self.gen_expr(v))
            .collect::<Result<Vec<_>, _>>()?;

        let ty = if !members.is_empty() {
            let first = members.first().unwrap();
            for member in members.iter().skip(1) {
                if member.ty() != first.ty() {
                    self.err
                        .err("Array values must be homogeneous".into(), member.span());
                    break; // only emit one err
                }
            }
            first.ty().clone()
        } else {
            sym::Type::Unknown
        };

        let ty = sym::Type::SizedArray(members.len(), Box::new(ty));

        let expr = ir::ExprKind::Array { members };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_struct_expr(
        &mut self,
        span: &ast::Span,
        type_name: &ast::Spanned<ast::Name>,
        members: &ast::SpanVec<(ast::Ident, ast::SpanBox<ast::Expr>)>,
    ) -> Result<ir::Expr, ModGenError> {
        let type_name_span = type_name.span.clone();
        let type_name = sym::Name::from_ast_name(type_name.value(), self.module.const_eval());
        let mut members: Vec<(String, _)> = members
            .iter()
            .map(|ast::Spanned { value: (id, v), .. }| {
                Ok((id.str().into(), Box::new(self.gen_expr(v)?)))
            })
            .collect::<Result<Vec<_>, ModGenError>>()?;

        let ty = if let Some(sym::SymbolInfo {
            symbol:
                sym::Symbol::Struct {
                    members: struct_members,
                    ..
                },
            ..
        }) = self.module.ty_ctx.root.resolve(&type_name)
        {
            if struct_members.len() != members.len() {
                self.err
                    .err("Missing or extra struct fields".into(), &type_name_span);
                sym::Type::Err
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
                                        sym::Type::Err,
                                    ),
                                );
                                // std::mem::
                                *expr_ref = self.coerce(expr, &member)?;
                            }
                            if expr.ty() != member {
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
                    sym::Type::Err
                } else {
                    sym::Type::Named(type_name.clone())
                }
            }
        } else {
            self.err.err("Invalid struct name".into(), &type_name_span);
            sym::Type::Err
        };

        let expr = ir::ExprKind::Struct { type_name, members };
        let expr = ir::Expr::new(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_expr_coerce(
        &mut self,
        expr: &ast::Spanned<ast::Expr>,
        ty: &sym::Type,
    ) -> Result<ir::Expr, ModGenError> {
        let expr = self.gen_expr(expr)?;
        self.coerce(expr, ty)
    }

    fn coerce(&mut self, expr: ir::Expr, ty: &sym::Type) -> Result<ir::Expr, ModGenError> {
        let expr_span = expr.span().clone();
        match (ty, expr.ty()) {
            (sym::Type::Pointer(ptr_kind, inner_ty), sym::Type::Pointer(_, _))
                if matches!(expr.kind(), ir::ExprKind::Null) =>
            {
                let expr = ir::ExprKind::Cast(
                    Box::new(expr),
                    Box::new(sym::Type::Pointer(ptr_kind.clone(), inner_ty.clone())),
                );
                let expr = ir::Expr::new(
                    expr,
                    expr_span,
                    sym::Type::Pointer(ptr_kind.clone(), inner_ty.clone()),
                );
                Ok(expr)
            }
            (sym::Type::Pointer(ptr_kind, inner_ty), sym::Type::Pointer(_, _))
                if matches!(
                    inner_ty.as_ref(),
                    sym::Type::Primitive(sym::PrimitiveType::Void)
                ) =>
            {
                let expr = ir::ExprKind::Cast(
                    Box::new(expr),
                    Box::new(sym::Type::Pointer(ptr_kind.clone(), inner_ty.clone())),
                );
                let expr = ir::Expr::new(
                    expr,
                    expr_span,
                    sym::Type::Pointer(ptr_kind.clone(), inner_ty.clone()),
                );
                Ok(expr)
            }
            (sym::Type::Primitive(target), sym::Type::Primitive(current))
                if current.is_integral() && target.is_integral() && target < current =>
            {
                let expr = ir::ExprKind::Cast(
                    Box::new(expr),
                    Box::new(sym::Type::Primitive(target.clone())),
                );
                let expr = ir::Expr::new(expr, expr_span, sym::Type::Primitive(target.clone()));
                Ok(expr)
            }
            _ => Ok(expr),
        }
    }

    fn gen_expr(&mut self, expr: &ast::Spanned<ast::Expr>) -> Result<ir::Expr, ModGenError> {
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
                sym::Type::Pointer(
                    sym::PointerType::Star,
                    Box::new(sym::Type::Primitive(sym::PrimitiveType::Void)),
                ),
            ),
        };
        Ok(expr)
    }
}
