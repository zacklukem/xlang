//! Handles generation of the IR

mod ir_gen_match;
use crate::ast;
use crate::error_context::ErrorContext;
use crate::infer::InferCtx;
use crate::intern::Int;
use crate::ir;
use crate::mod_gen::{ModGenError, TypeGenerator};
use crate::ty;
use std::collections::{HashMap, VecDeque};
use std::iter::Iterator;

#[allow(clippy::too_many_arguments)]
pub fn gen_fun_block<'ast, 'ty, 'mg>(
    usages: &'mg HashMap<String, ir::Path>,
    module: &'mg ir::Module<'ty>,
    db_name: String,
    err: &'mg mut ErrorContext,
    def_id: ir::DefId,
    params: Vec<(String, ty::Ty<'ty>)>,
    return_type: ty::Ty<'ty>,
    fun: &'ast ast::SpanBox<ast::FunBlock>,
    current_generics: Vec<String>,
) -> Result<ir::Fun<'ty>, ModGenError> {
    let (block, variable_defs) = {
        let mut ir_gen = IrGen {
            icx: InferCtx::new(module.ty_ctx),
            usages,
            var_id: 0,
            md: module,
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
        let variable_defs = ir_gen.variable_defs().into_iter().collect();
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

    fn resolve(&self, name: &str) -> Option<&String> {
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

struct IrGen<'ty, 'mg> {
    var_id: u32,
    md: &'mg ir::Module<'ty>,
    err: &'mg mut ErrorContext,
    usages: &'mg HashMap<String, ir::Path>,
    scope: Box<Scope>,
    /// types of variables (variable scoped)
    params: HashMap<String, ty::Ty<'ty>>,
    variable_defs: HashMap<String, ty::Ty<'ty>>,
    continue_break_label: Vec<String>,
    label_next: Option<String>,
    return_type: ty::Ty<'ty>,
    current_generics: Vec<String>,
    icx: InferCtx<'ty>,
}

fn continue_label(v: &str) -> String {
    format!("{}_continue", v)
}

fn break_label(v: &str) -> String {
    format!("{}_break", v)
}

impl<'ast, 'ty, 'mg> TypeGenerator<'ast, 'ty> for IrGen<'ty, 'mg> {
    fn current_generics(&self) -> &[String] {
        &self.current_generics
    }

    fn module(&self) -> &ir::Module<'ty> {
        self.md
    }
    fn mod_path(&self) -> &ir::Path {
        todo!();
    }

    fn usages(&self) -> &HashMap<String, ir::Path> {
        self.usages
    }

    fn err(&mut self) -> &mut ErrorContext {
        self.err
    }
}

impl<'ty, 'ast, 'mg> IrGen<'ty, 'mg> {
    fn variable_defs(self) -> HashMap<String, ty::Ty<'ty>> {
        self.variable_defs
    }

    fn get_var_id(&mut self) -> u32 {
        let n = self.var_id;
        self.var_id += 1;
        n
    }

    fn in_scope<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old_scope = std::mem::take(&mut self.scope);
        self.scope.parent = Some(old_scope);
        let r = f(self);
        let parent = std::mem::take(&mut self.scope.parent);
        self.scope = parent.unwrap();
        r
    }

    fn declare_var(&mut self, block_scope_name: &str, ty: ty::Ty<'ty>) -> String {
        let id = self.get_var_id();
        let fun_scope_name = format!("{}_{}", block_scope_name, id);
        self.variable_defs.insert(fun_scope_name.clone(), ty);
        self.scope
            .insert(block_scope_name.into(), fun_scope_name.clone());
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

    fn replace_generics(&self, ty: ty::Ty<'ty>, generics: &[(String, ty::Ty<'ty>)]) -> ty::Ty<'ty> {
        crate::generics::replace_generics(self.md.ty_ctx(), ty, generics)
    }

    /// Returns the type of the name and a boolean which is true if the name islocal scoped and false if it is global scoped
    fn resolve_value(
        &self,
        name: &ir::Path,
        generics: &[ty::Ty<'ty>],
    ) -> Option<(ty::Ty<'ty>, Option<String>)> {
        if let ir::Path::Terminal(id) = name {
            if let Some(var) = self.scope.resolve(id) {
                return self
                    .variable_defs
                    .get(var)
                    .cloned()
                    .or_else(|| self.params.get(var).cloned())
                    .map(|v| (v, Some(var.clone())));
            }
        }
        match self.md.get_def_by_path(name) {
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
                let generics = if !generics.is_empty() {
                    // if ty_params.len() != generics.len() {
                    //     self.err.err("Missing or extra generics".into(),
                    // need a span here
                    assert_eq!(ty_params.len(), generics.len(), "Mismatched generics count");
                    // }
                    generics.to_owned()
                } else {
                    ty_params.iter().map(|_| self.icx.mk_var()).collect()
                };
                let params = params.iter().map(|(_, t)| *t).collect::<Vec<_>>();
                Some((
                    self.replace_generics(
                        self.md.ty_ctx().int(ty::TyKind::Fun(params, *return_type)),
                        &Iterator::zip(ty_params.iter(), generics.iter())
                            .map(|(a, b)| (a.clone(), *b))
                            .collect::<Vec<_>>(),
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
        body: &'ast ast::SpanSlice<ast::Stmt>,
        close_brace: &ast::Span,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
        self.in_scope(|this| {
            let mut stmts = Vec::new();
            for stmt in body {
                stmts.push(this.gen_stmt(stmt)?);
            }
            let label_next = std::mem::take(&mut this.label_next);
            if let Some(label) = label_next {
                stmts.push(ir::Stmt::new(
                    ir::StmtKind::Labeled(label, None),
                    close_brace.clone(),
                ))
            }
            Ok(ir::StmtKind::Block(stmts))
        })
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

        let condition = Box::new(self.md.mk_const_bool(true, span.clone()));

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

    fn gen_for_range_stmt(
        &mut self,
        span: &ast::Span,
        label: Option<&ast::Ident>,
        initializer: &ast::Spanned<ast::Pattern>,
        range: &ast::Spanned<ast::Expr>,
        block: &ast::Spanned<ast::Stmt>,
    ) -> Result<ir::StmtKind<'ty>, ModGenError> {
        let label_prefix = label
            .map(|v| v.str().into())
            .unwrap_or_else(|| format!("for_{}", self.get_var_id()));

        self.continue_break_label.push(label_prefix.clone());

        let init_span = &initializer.span;
        let initializer = if let ast::Pattern::Ident(name) = initializer.value() {
            name.value().ident_str().unwrap()
        } else {
            todo!();
        };
        let usize_ty = ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::USize);
        let expr = self.gen_expr(range)?;
        let (from, to): (Box<ir::Expr<'ty>>, Box<ir::Expr<'ty>>) = match expr.kind {
            ir::ExprKind::Range(from, to) => (from, to),
            ir::ExprKind::RangeFrom(to) => {
                (Box::new(self.md.mk_const_usize(0, init_span.clone())), to)
            }
            _ => todo!(),
        };

        self.in_scope(|this| {
            let initializer = this.declare_var(&initializer, usize_ty);
            let initializer = ir::ExprKind::Ident(initializer);
            let initializer = this.md.mk_expr(initializer, init_span.clone(), usize_ty);
            let initializer_stmt = this
                .md
                .mk_expr(
                    ir::ExprKind::Assign(Box::new(initializer.clone()), ir::AssignOp::Eq, from),
                    init_span.clone(),
                    usize_ty,
                )
                .stmt();
            let condition = Box::new(this.md.mk_expr(
                ir::ExprKind::Binary(Box::new(initializer.clone()), ir::BinOp::Lt, to),
                init_span.clone(),
                usize_ty,
            ));
            let incrementor = Box::new(this.md.mk_assign_expr(
                initializer.clone(),
                ir::AssignOp::AddEq,
                this.md.mk_const_usize(1, init_span.clone()),
            ));
            let block = Box::new(this.gen_stmt(block)?);

            let popped_prefix = this.continue_break_label.pop().unwrap();

            assert_eq!(popped_prefix, label_prefix);
            let stmt = ir::StmtKind::For {
                initializer: Box::new(initializer_stmt),
                condition,
                incrementor,
                block,
            };

            let stmt = ir::StmtKind::Labeled(
                continue_label(&label_prefix),
                Some(Box::new(ir::Stmt::new(stmt, span.clone()))),
            );
            this.label_next(break_label(&label_prefix));

            Ok(stmt)
        })
    }

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
                let global_var_name = self.declare_hidden_var(ty);
                let lhs_expr = ir::ExprKind::Ident(global_var_name.clone());
                let lhs_expr = self.md.mk_expr(lhs_expr, span.clone(), ty);
                let assign_expr = self.md.mk_assign_expr(lhs_expr, ir::AssignOp::Eq, expr);
                out.push(ir::StmtKind::Expr(Box::new(assign_expr)));

                if let ty::Ty(Int(ty::TyKind::Tuple(tys))) = &ty {
                    if tys.len() != patterns.len() {
                        self.err.err("Incompatible pattern types".into(), span);
                    }
                    for (i, (pattern, pat_ty)) in patterns.iter().zip(tys.iter()).enumerate() {
                        let access_expr = ir::ExprKind::Ident(global_var_name.clone());
                        let access_expr = self.md.mk_expr(access_expr, span.clone(), ty);

                        let expr = ir::ExprKind::Dot(Box::new(access_expr), format!("_{}", i));
                        let expr = self.md.mk_expr(expr, span.clone(), *pat_ty);

                        self.gen_let_stmt_patterned(out, span, pattern, *pat_ty, expr)?;
                    }
                } else {
                    self.err.err("Incompatible pattern types".into(), span);
                }
            }
            ast::Pattern::Ident(id) if matches!(id.value(), ast::Name::Ident(..)) => {
                let id = if let ast::Name::Ident(name, _) = id.value() {
                    name
                } else {
                    panic!();
                };
                let expr = self.coerce(
                    expr,
                    ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::I32),
                )?;
                let ty = self.md.ty_of(&expr);
                let global_var_name = self.declare_var(id.str(), ty);
                let lhs_expr = ir::ExprKind::Ident(global_var_name);
                let lhs_expr = self.md.mk_expr(lhs_expr, id.span.clone(), ty);
                let assign_expr = self.md.mk_assign_expr(lhs_expr, ir::AssignOp::Eq, expr);
                out.push(ir::StmtKind::Expr(Box::new(assign_expr)));
            }
            _ => todo!(),
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
            self.md.ty_of(&expr)
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
            let label = self.continue_break_label.last().map(|v| map_fn(v));
            if let Some(label) = label {
                label
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
            Some(e) => self.md.ty_of(e),
            None => ty::void_ty(self.md.ty_ctx()),
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
                label,
                initializer,
                range,
                block,
                ..
            } => self.gen_for_range_stmt(
                &stmt.span,
                label.as_ref(),
                initializer.as_ref(),
                range.as_ref(),
                block,
            )?,

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

            ast::Stmt::Case { expr, arms, .. } => self.gen_case(expr, arms)?,

            ast::Stmt::Expr(expr) => ir::StmtKind::Expr(Box::new(self.gen_expr(expr)?)),
            ast::Stmt::InlineC {
                inputs,
                outputs,
                code,
                ..
            } => {
                let inputs = inputs
                    .iter()
                    .map(|(pt, varname, replace_name)| {
                        let varname: String = match pt {
                            ast::InlineCParamType::Var => {
                                self.scope.resolve(varname.str()).unwrap().clone()
                            }
                            _ => varname.str().into(),
                        };
                        (pt.into(), varname, replace_name.str().into())
                    })
                    .collect();
                let outputs = outputs
                    .iter()
                    .map(|(replace_name, pt, varname)| {
                        let varname = self.scope.resolve(varname.str()).unwrap();
                        (replace_name.str().into(), pt.into(), varname.clone())
                    })
                    .collect();
                let code = code.str().into();
                ir::StmtKind::InlineC {
                    inputs,
                    outputs,
                    code,
                }
            }
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
        let (ty, var_name) = ty.unwrap_or_else(|| (ty::err_ty(self.md.ty_ctx()), None));
        let expr = if let Some(var) = var_name {
            // self.scope.resolve(&id)
            ir::ExprKind::Ident(var)
        } else {
            ir::ExprKind::GlobalIdent(name, generics)
        };
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
        let expr = self.md.mk_expr(
            kind,
            span.clone(),
            ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::Integer),
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
        let expr = self.md.mk_expr(
            kind,
            span.clone(),
            ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::F64),
        );
        Ok(expr)
    }

    fn gen_string_expr(&mut self, span: &ast::Span) -> Result<ir::Expr<'ty>, ModGenError> {
        let value = span.str().into();
        let kind = ir::ExprKind::String(value);
        let expr = self.md.mk_expr(
            kind,
            span.clone(),
            ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::U8)
                .slice_ty(self.md.ty_ctx())
                .ptr(self.md.ty_ctx()),
        );
        Ok(expr)
    }

    fn gen_bool_expr(
        &mut self,
        span: &ast::Span,
        value: bool,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let kind = ir::ExprKind::Bool(value);
        let expr = self.md.mk_expr(
            kind,
            span.clone(),
            ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::Bool),
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
        values: &'ast ast::SpanSlice<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let values = self.gen_expr_iter(values.iter())?;

        let ty = self.md.ty_ctx().int(ty::TyKind::Tuple(
            values.iter().map(|v| self.md.ty_of(v)).collect(),
        ));
        let expr = ir::ExprKind::Tuple(values);
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
        let lhs_ty = self.md.ty_of(&lhs);
        let lhs = lhs;
        let op = op.value().into();
        let rhs = self.gen_expr_coerce(rhs, lhs_ty)?;

        let ty = if lhs_ty != self.md.ty_of(&rhs) {
            self.err.err(
                format!("Incompatible types {} and {}", lhs_ty, self.md.ty_of(&rhs)),
                span,
            );
            ty::err_ty(self.md.ty_ctx())
        } else {
            lhs_ty
        };

        let expr = ir::ExprKind::Assign(Box::new(lhs), op, Box::new(rhs));
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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

        let (lhs, rhs) = match (self.md.ty_of(&lhs), self.md.ty_of(&rhs)) {
            (ty::Ty(Int(ty::TyKind::Pointer(_, _))), ty::Ty(Int(ty::TyKind::Pointer(_, _)))) => {
                let ty = ty::void_ty(self.md.ty_ctx()).ptr(self.md.ty_ctx());
                (self.coerce(lhs, ty)?, self.coerce(rhs, ty)?)
            }
            (
                ty::Ty(Int(ty::TyKind::Primitive(lhs_ty))),
                ty::Ty(Int(ty::TyKind::Primitive(rhs_ty))),
            ) => {
                let ty = lhs_ty.min(rhs_ty).clone();
                let ty = self.md.ty_ctx().int(ty::TyKind::Primitive(ty));
                (self.coerce(lhs, ty)?, self.coerce(rhs, ty)?)
            }
            _ => (lhs, rhs),
        };

        if self.md.ty_of(&lhs) != self.md.ty_of(&rhs) {
            self.err.err(
                format!(
                    "Incompatible types {} <> {}",
                    self.md.ty_of(&lhs),
                    self.md.ty_of(&rhs)
                ),
                span,
            );
        }

        let ty = match op {
            ir::BinOp::AndAnd | ir::BinOp::OrOr => {
                if let ty::Ty(Int(ty::TyKind::Primitive(ty::PrimitiveType::Bool))) =
                    self.md.ty_of(&lhs)
                {
                    self.md.ty_of(&lhs)
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.md.ty_ctx())
                }
            }
            ir::BinOp::Lt
            | ir::BinOp::Gt
            | ir::BinOp::LtEq
            | ir::BinOp::GtEq
            | ir::BinOp::EqEq
            | ir::BinOp::NotEq
                if self.md.ty_of(&lhs).is_numeric()
                    || matches!(self.md.ty_of(&lhs), ty::Ty(Int(ty::TyKind::Pointer(_, _)))) =>
            {
                ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::Bool)
            }
            _ if !self.md.ty_of(&lhs).is_numeric() => {
                self.err.err("Incompatible types".into(), span);
                ty::err_ty(self.md.ty_ctx())
            }
            _ => self.md.ty_of(&lhs),
        };

        let expr = ir::ExprKind::Binary(Box::new(lhs), op, Box::new(rhs));
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot if self.md.ty_of(&rhs).is_numeric() => {
                self.md.ty_of(&rhs)
            }
            ir::UnaryOp::Neg | ir::UnaryOp::BitNot => {
                self.err.err("Incompatible types".into(), span);
                ty::err_ty(self.md.ty_ctx())
            }
            ir::UnaryOp::LogNot => {
                if let ty::Ty(Int(ty::TyKind::Primitive(ty::PrimitiveType::Bool))) =
                    self.md.ty_of(&rhs)
                {
                    self.md.ty_of(&rhs)
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.md.ty_ctx())
                }
            }

            ir::UnaryOp::Deref => {
                if let ty::Ty(Int(ty::TyKind::Pointer(_mutable, ty))) = self.md.ty_of(&rhs) {
                    *ty
                } else {
                    self.err.err("Incompatible types".into(), span);
                    ty::err_ty(self.md.ty_ctx())
                }
            }

            ir::UnaryOp::Ref => self.md.ty_of(&rhs).ptr(self.md.ty_ctx()),

            ir::UnaryOp::RefMut => self.md.ty_of(&rhs).ptr(self.md.ty_ctx()),

            ir::UnaryOp::Box => self.md.ty_of(&rhs).ptr(self.md.ty_ctx()),
        };

        let expr = ir::ExprKind::Unary(op, Box::new(rhs));
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
        while let ty::Ty(Int(ty::TyKind::Pointer(_mutable, ty))) = self.md.ty_of(&lhs) {
            lhs = self.md.mk_expr(
                ir::ExprKind::Unary(ir::UnaryOp::Deref, Box::new(lhs)),
                span.clone(),
                *ty,
            );
        }

        let ty = match self.md.ty_of(&lhs).0 .0 {
            ty::TyKind::Adt(ty::AdtType {
                def_id,
                ty_params: instance_ty_params,
                ..
            }) => {
                let def = self.md.get_def_by_id(*def_id);
                match def {
                    ir::Def {
                        kind:
                            ir::DefKind::Struct {
                                members,
                                symbols,
                                ty_params: struct_ty_params,
                            },
                        ..
                    } => {
                        assert_eq!(instance_ty_params.len(), struct_ty_params.len());
                        if let Some(def_id) = symbols.get(&rhs) {
                            let def = self.md.get_def_by_id(*def_id);
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

                                    let typ_iter = Iterator::zip(
                                        fun_ty_params.iter(),
                                        instance_ty_params.iter(),
                                    )
                                    .map(|(a, b)| (a.clone(), *b))
                                    .collect::<Vec<_>>();

                                    let params = params
                                        .iter()
                                        .map(|(_, t)| self.replace_generics(*t, &typ_iter))
                                        .collect();

                                    let return_type =
                                        self.replace_generics(*return_type, &typ_iter);

                                    let ty =
                                        self.md.ty_ctx().int(ty::TyKind::Fun(params, return_type));

                                    let pass_ty_ref = self.md.ty_of(&lhs).ptr(self.md.ty_ctx());

                                    let pass_expr =
                                        ir::ExprKind::Unary(ir::UnaryOp::Ref, Box::new(lhs));
                                    let pass_expr =
                                        self.md.mk_expr(pass_expr, span.clone(), pass_ty_ref);

                                    // Struct::method
                                    let path = self.md.get_path_by_def_id(*def_id);
                                    let expr = ir::ExprKind::GlobalIdent(
                                        path.clone(),
                                        instance_ty_params.clone(),
                                    );
                                    let expr = self.md.mk_expr_pass(
                                        expr,
                                        span.clone(),
                                        ty,
                                        Box::new(pass_expr),
                                    );
                                    return Ok(expr);
                                }
                                _ => todo!("error"),
                            }
                        } else if let Some(ty) = members.get(&rhs) {
                            let generics =
                                Iterator::zip(struct_ty_params.iter(), instance_ty_params.iter())
                                    .map(|(a, b)| (a.clone(), *b))
                                    .collect::<Vec<_>>();
                            self.replace_generics(*ty, &generics)
                        } else {
                            self.err.err("Field not found in struct".into(), span);
                            ty::err_ty(self.md.ty_ctx())
                        }
                    }
                    ir::Def {
                        kind:
                            ir::DefKind::Enum {
                                symbols,
                                ty_params: struct_ty_params,
                                ..
                            },
                        ..
                    } => {
                        assert_eq!(instance_ty_params.len(), struct_ty_params.len());
                        if let Some(def_id) = symbols.get(&rhs) {
                            let def = self.md.get_def_by_id(*def_id);
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

                                    let typ_iter = Iterator::zip(
                                        fun_ty_params.iter(),
                                        instance_ty_params.iter(),
                                    )
                                    .map(|(a, b)| (a.clone(), *b))
                                    .collect::<Vec<_>>();

                                    let params = params
                                        .iter()
                                        .map(|(_, t)| self.replace_generics(*t, &typ_iter))
                                        .collect();

                                    let return_type =
                                        self.replace_generics(*return_type, &typ_iter);

                                    let ty =
                                        self.md.ty_ctx().int(ty::TyKind::Fun(params, return_type));

                                    let pass_ty_ref = self.md.ty_of(&lhs).ptr(self.md.ty_ctx());

                                    let pass_expr =
                                        ir::ExprKind::Unary(ir::UnaryOp::Ref, Box::new(lhs));
                                    let pass_expr =
                                        self.md.mk_expr(pass_expr, span.clone(), pass_ty_ref);

                                    // Struct::method
                                    let path = self.md.get_path_by_def_id(*def_id);
                                    let expr = ir::ExprKind::GlobalIdent(
                                        path.clone(),
                                        instance_ty_params.clone(),
                                    );
                                    let expr = self.md.mk_expr_pass(
                                        expr,
                                        span.clone(),
                                        ty,
                                        Box::new(pass_expr),
                                    );
                                    return Ok(expr);
                                }
                                _ => todo!("error"),
                            }
                        } else {
                            self.err.err("Field not found in enum".into(), span);
                            ty::err_ty(self.md.ty_ctx())
                        }
                    }
                    _ => {
                        self.err
                            .err("The dot operator can only be used on a struct".into(), span);
                        ty::err_ty(self.md.ty_ctx())
                    }
                }
            }
            _ => {
                self.err
                    .err("The dot operator can only be used on a struct".into(), span);
                ty::err_ty(self.md.ty_ctx())
            }
        };

        let expr = ir::ExprKind::Dot(Box::new(lhs), rhs);
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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

        let ty = match (self.md.ty_of(&expr).0 .0, ty.0 .0) {
            (
                ty::TyKind::Primitive(ty::PrimitiveType::Void),
                ty::TyKind::Primitive(ty::PrimitiveType::Void),
            ) => {
                self.err.err("Cannot cast void".into(), span);
                ty::err_ty(self.md.ty_ctx())
            }
            (
                ty::TyKind::Primitive(ty::PrimitiveType::Bool),
                ty::TyKind::Primitive(ty::PrimitiveType::Bool),
            ) => {
                self.err.err("Cannot cast bool".into(), span);
                ty::err_ty(self.md.ty_ctx())
            }
            _ => ty,
        };

        let expr = ir::ExprKind::Cast(Box::new(expr), ty);
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
        let else_expr = self.gen_expr_coerce(else_expr, self.md.ty_of(&then_expr))?;

        match self.md.ty_of(&condition).0 .0 {
            ty::TyKind::Primitive(ty::PrimitiveType::Bool) => (),
            _ => {
                self.err.err(
                    "If statement condition must be bool type".into(),
                    condition.span(),
                );
            }
        }

        let ty = if self.md.ty_of(&then_expr) == self.md.ty_of(&else_expr) {
            self.md.ty_of(&then_expr)
        } else {
            self.err.err(
                "If and else value types don't match".into(),
                then_expr.span(),
            );
            ty::err_ty(self.md.ty_ctx())
        };

        let condition = Box::new(condition);
        let then_expr = Box::new(then_expr);
        let else_expr = Box::new(else_expr);

        let expr = ir::ExprKind::Ternary {
            condition,
            then_expr,
            else_expr,
        };

        let expr = self.md.mk_expr(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_range_expr(
        &mut self,
        span: &ast::Span,
        range: &ast::Range,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        macro_rules! zero {
            () => {
                self.md.mk_const_usize(0, span.clone())
            };
        }
        macro_rules! check_type {
            ($e: expr) => {
                if matches!($e.0.0, ty::TyKind::Primitive(ty::PrimitiveType::USize)) {
                    self.err.err("Range values must be usize".into(), span);
                }
            };
        }
        let expr = match range {
            ast::Range::All(_) => ir::ExprKind::RangeFrom(Box::new(zero!())),
            ast::Range::Full(lhs, _, rhs) => {
                let lhs = self.gen_expr(lhs.as_ref())?;
                let rhs = self.gen_expr(rhs.as_ref())?;
                check_type!(self.md.ty_of(&lhs));
                check_type!(self.md.ty_of(&rhs));
                ir::ExprKind::Range(Box::new(lhs), Box::new(rhs))
            }
            ast::Range::Start(lhs, _) => {
                let lhs = self.gen_expr(lhs.as_ref())?;
                check_type!(self.md.ty_of(&lhs));
                ir::ExprKind::RangeFrom(Box::new(lhs))
            }
            ast::Range::End(_, rhs) => {
                let rhs = self.gen_expr(rhs.as_ref())?;
                check_type!(self.md.ty_of(&rhs));
                ir::ExprKind::Range(Box::new(zero!()), Box::new(rhs))
            }
        };

        let expr = self
            .md
            .mk_expr(expr, span.clone(), ty::range_ty(self.md.ty_ctx()));
        Ok(expr)
    }

    fn gen_call_expr(
        &mut self,
        span: &ast::Span,
        expr: &ast::Spanned<ast::Expr>,
        arguments: &ast::SpanSlice<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let mut expr = self.gen_expr(expr)?;

        let fun_pass = std::mem::take(expr.fun_pass_mut());

        let (params, return_type) = match self.md.ty_of(&expr).0 .0 {
            ty::TyKind::Fun(params, return_type) => (params, return_type),
            _ => {
                self.err.err("Expected function type".into(), span);
                return Ok(self.md.mk_expr(
                    ir::ExprKind::Err,
                    span.clone(),
                    ty::err_ty(self.md.ty_ctx()),
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
            ty::err_ty(self.md.ty_ctx())
        } else {
            for (p_ty, ir::Expr { id, span, .. }) in params.iter().zip(arguments.iter()) {
                let ty = self.md.ty_of(*id);
                if *p_ty != ty {
                    self.err
                        .err(format!("Invalid argument type {} {}", p_ty, ty), span);
                }
            }
            *return_type
        };

        let expr = Box::new(expr);

        let expr = ir::ExprKind::Call { expr, arguments };
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
            ty::primitive_ty(self.md.ty_ctx(), ty::PrimitiveType::USize),
        )?;

        let ty = match (self.md.ty_of(&expr).0 .0, self.md.ty_of(&index).0 .0) {
            (
                ty::TyKind::Pointer(_, inner_type),
                ty::TyKind::Primitive(ty::PrimitiveType::USize),
            ) => *inner_type,
            _ => ty::err_ty(self.md.ty_ctx()),
        };

        let expr = Box::new(expr);
        let index = Box::new(index);

        let expr = ir::ExprKind::Index { expr, index };
        let expr = self.md.mk_expr(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_array_expr(
        &mut self,
        span: &ast::Span,
        members: &ast::SpanSlice<ast::Expr>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let members = self.gen_expr_iter(members.iter())?;

        let ty = if !members.is_empty() {
            let first = members.first().unwrap();
            let first_ty = self.md.ty_of(first);
            for member in members.iter().skip(1) {
                if self.md.ty_of(member) != first_ty {
                    self.err
                        .err("Array values must be homogeneous".into(), member.span());
                    break; // only emit one err
                }
            }
            first_ty
        } else {
            todo!()
        };

        let ty = self
            .md
            .ty_ctx()
            .int(ty::TyKind::SizedArray(members.len(), ty));

        let expr = ir::ExprKind::Array { members };
        let expr = self.md.mk_expr(expr, span.clone(), ty);
        Ok(expr)
    }

    fn gen_struct_expr(
        &mut self,
        span: &ast::Span,
        type_name: &ast::Spanned<ast::Name>,
        members: &ast::SpanSlice<(ast::Ident, ast::SpanBox<ast::Expr>)>,
    ) -> Result<ir::Expr<'ty>, ModGenError> {
        let type_name_span = type_name.span.clone();
        let (type_name, type_generics) = self.gen_path_and_generics(type_name.value())?;
        let mut members: Vec<(String, _)> = {
            let mut out = Vec::with_capacity(members.len());
            for ast::Spanned { value: (id, v), .. } in members {
                out.push((id.str().into(), Box::new(self.gen_expr(v)?)))
            }
            out
        };

        let ty = if let Some(ir::Def {
            kind:
                ir::DefKind::Struct {
                    members: struct_members,
                    ..
                },
            ..
        }) = self.md.get_def_by_path(&type_name)
        {
            let def_id = self.md.get_def_id_by_path(&type_name).unwrap();
            if struct_members.len() != members.len() {
                self.err
                    .err("Missing or extra struct fields".into(), &type_name_span);
                ty::err_ty(self.md.ty_ctx())
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
                                    self.md.mk_expr(
                                        ir::ExprKind::Err,
                                        ast::Span::dummy(),
                                        ty::err_ty(self.md.ty_ctx()),
                                    ),
                                );
                                *expr_ref = self.coerce(expr, *member)?;
                            }
                            if self.md.ty_of(&**expr) != *member {
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
                    ty::err_ty(self.md.ty_ctx())
                } else {
                    self.md.ty_ctx().int(ty::TyKind::Adt(ty::AdtType {
                        def_id,
                        path: type_name,
                        ty_params: type_generics,
                    }))
                }
            }
        } else {
            self.err.err("Invalid struct name".into(), &type_name_span);
            ty::err_ty(self.md.ty_ctx())
        };
        let expr = ir::ExprKind::Struct { ty, members };
        let expr = self.md.mk_expr(expr, span.clone(), ty);
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
        match (ty.0 .0, self.md.ty_of(&expr).0 .0) {
            (ty::TyKind::Pointer(ptr_kind, inner_ty), ty::TyKind::Pointer(_, _))
                if matches!(expr.kind(), ir::ExprKind::Null) =>
            {
                let ty = self
                    .md
                    .ty_ctx()
                    .int(ty::TyKind::Pointer(ptr_kind.clone(), *inner_ty));
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = self.md.mk_expr(expr, expr_span, ty);
                Ok(expr)
            }
            (ty::TyKind::Pointer(ptr_kind, inner_ty), ty::TyKind::Pointer(_, _))
                if matches!(
                    inner_ty.0 .0,
                    ty::TyKind::Primitive(ty::PrimitiveType::Void)
                ) =>
            {
                let ty = self
                    .md
                    .ty_ctx()
                    .int(ty::TyKind::Pointer(ptr_kind.clone(), *inner_ty));
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = self.md.mk_expr(expr, expr_span, ty);
                Ok(expr)
            }
            (ty::TyKind::Primitive(target), ty::TyKind::Primitive(ty::PrimitiveType::Integer))
                if target.is_integral() =>
            {
                let expr = ir::ExprKind::Cast(Box::new(expr), ty);
                let expr = self.md.mk_expr(expr, expr_span, ty);
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
            ast::Expr::Null(_) => self.md.mk_expr(
                ir::ExprKind::Null,
                expr_span.clone(),
                ty::void_ty(self.md.ty_ctx()).ptr(self.md.ty_ctx()),
            ),
            ast::Expr::MacroCall(cell) => {
                let expr = cell.borrow();
                let expr = expr.as_ref().right().unwrap();
                self.gen_expr(expr.as_ref())?
            }
        };
        Ok(expr)
    }
}
