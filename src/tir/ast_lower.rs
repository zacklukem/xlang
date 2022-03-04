use either::Either;

use super::*;
use crate::ast::{self, Spanned};
use crate::error_context::ErrorContext;
use crate::ir::{self};
use crate::mod_gen::{ModGenError, TypeGenerator};

pub fn lower_ast<'ty>(
    md: &ir::Module<'ty>,
    tir: &TirCtx<'ty>,
    err: &mut ErrorContext,
    usages: &HashMap<String, ir::Path>,
    current_generics: Vec<String>,
    fun_block: &ast::Spanned<ast::FunBlock>,
) -> Result<Stmt<'ty>, ModGenError> {
    (AstLowering {
        md,
        tir,
        err,
        usages,
        current_generics,
    })
    .fun_block(fun_block)
}

struct AstLowering<'a, 'ty> {
    md: &'a ir::Module<'ty>,
    tir: &'a TirCtx<'ty>,
    err: &'a mut ErrorContext,
    usages: &'a HashMap<String, ir::Path>,
    current_generics: Vec<String>,
}

impl<'ast, 'ty, 'a> TypeGenerator<'ast, 'ty> for AstLowering<'a, 'ty> {
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

impl<'a, 'ty> AstLowering<'a, 'ty> {
    fn fun_block(&mut self, body: &Spanned<ast::FunBlock>) -> Result<Stmt<'ty>, ModGenError> {
        let mut stmts = Vec::new();
        for stmt in &body.value().stmts {
            stmts.push(self.stmt(stmt)?);
        }
        Ok(self.tir.mk_stmt(StmtKind::Block(stmts), body.span.clone()))
    }

    fn stmt(&mut self, stmt: &Spanned<ast::Stmt>) -> Result<Stmt<'ty>, ModGenError> {
        let stmt_kind = match stmt.value() {
            ast::Stmt::If {
                condition,
                block,
                else_block,
                ..
            } => StmtKind::If {
                condition: Box::new(self.expr(condition)?),
                block: Box::new(self.stmt(block)?),
                else_block: else_block
                    .as_ref()
                    .map(|stmt| self.stmt(stmt))
                    .transpose()?
                    .map(Box::new),
            },

            ast::Stmt::While {
                label,
                condition,
                block,
                ..
            } => StmtKind::While {
                label: label.as_ref().map(|v| v.str().to_owned()),
                condition: Box::new(self.expr(condition)?),
                block: Box::new(self.stmt(block)?),
            },

            ast::Stmt::Loop { label, block, .. } => StmtKind::Loop {
                label: label.as_ref().map(|v| v.str().to_owned()),
                block: Box::new(self.stmt(block)?),
            },

            ast::Stmt::Case { expr, arms, .. } => {
                let expr = Box::new(self.expr(expr)?);
                let arms = arms
                    .iter()
                    .map(|arm| {
                        Ok(Arm {
                            pattern: Box::new(self.pattern(arm.value().pattern.as_ref())?),
                            stmts: arm
                                .value()
                                .stmts
                                .iter()
                                .map(|stmt| self.stmt(stmt))
                                .collect::<Result<Vec<_>, ModGenError>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                StmtKind::Case { expr, arms }
            }

            ast::Stmt::ForRange {
                label,
                initializer,
                range,
                block,
                ..
            } => StmtKind::ForRange {
                label: label.as_ref().map(|v| v.str().to_owned()),
                initializer: Box::new(self.pattern(initializer)?),
                range: Box::new(self.expr(range)?),
                block: Box::new(self.stmt(block)?),
            },

            ast::Stmt::Let {
                mut_tok,
                pattern,
                type_name,
                expr,
                ..
            } => StmtKind::Let {
                mutable: mut_tok.is_some(),
                pattern: Box::new(self.pattern(pattern)?),
                type_name: type_name.as_ref().map(|ty| self.gen_type(ty)).transpose()?,
                expr: Box::new(self.expr(expr)?),
            },

            ast::Stmt::InlineC {
                inputs,
                outputs,
                code,
                ..
            } => {
                let inputs = inputs
                    .iter()
                    .map(|(pt, varname, replace_name)| {
                        (
                            pt.into(),
                            varname.str().to_owned(),
                            replace_name.str().into(),
                        )
                    })
                    .collect();
                let outputs = outputs
                    .iter()
                    .map(|(replace_name, pt, varname)| {
                        (
                            replace_name.str().into(),
                            pt.into(),
                            varname.str().to_owned(),
                        )
                    })
                    .collect();
                let code = code.str().into();
                StmtKind::InlineC {
                    inputs,
                    outputs,
                    code,
                }
            }

            ast::Stmt::Block(_, stmts, _) => StmtKind::Block(
                stmts
                    .iter()
                    .map(|stmt| self.stmt(stmt))
                    .collect::<Result<Vec<_>, ModGenError>>()?,
            ),
            ast::Stmt::Return(_, expr) => StmtKind::Return(
                expr.as_ref()
                    .map(|expr| self.expr(expr))
                    .transpose()?
                    .map(Box::new),
            ),
            ast::Stmt::Continue(_, label) => {
                StmtKind::Continue(label.as_ref().map(|v| v.str().to_owned()))
            }
            ast::Stmt::Break(_, label) => {
                StmtKind::Break(label.as_ref().map(|v| v.str().to_owned()))
            }
            ast::Stmt::Expr(expr) => StmtKind::Expr(Box::new(self.expr(expr)?)),
        };
        Ok(self.tir.mk_stmt(stmt_kind, stmt.span.clone()))
    }

    fn expr(&mut self, expr: &Spanned<ast::Expr>) -> Result<Expr<'ty>, ModGenError> {
        let expr_kind = match expr.value() {
            ast::Expr::Ident(name) => {
                let (path, generics) = self.gen_path_and_generics(name)?;
                ExprKind::Ident(path, generics)
            }
            ast::Expr::Integer(val, _) => {
                let st = val.str();
                let kind = if st.contains('-') {
                    IntegerSpecifier::Signed(str::parse::<isize>(st).unwrap())
                } else {
                    IntegerSpecifier::Unsigned(str::parse::<usize>(st).unwrap())
                };
                ExprKind::Integer(kind)
            }
            ast::Expr::Float(val, _) => {
                let value = str::parse::<f64>(val.str()).unwrap();
                ExprKind::Float(FloatSpecifier::F64(value))
            }
            ast::Expr::String(val) => ExprKind::String(val.str().into()),
            ast::Expr::Bool(_, val) => ExprKind::Bool(*val),
            ast::Expr::Null(_) => ExprKind::Null,
            ast::Expr::Tuple(_, exprs, _) => {
                let exprs = exprs
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                ExprKind::Tuple(exprs)
            }
            ast::Expr::Assign(lhs, op, rhs) => ExprKind::Assign(
                Box::new(self.expr(lhs)?),
                op.value().into(),
                Box::new(self.expr(rhs)?),
            ),
            ast::Expr::Binary(lhs, op, rhs) => ExprKind::Binary(
                Box::new(self.expr(lhs)?),
                op.value().into(),
                Box::new(self.expr(rhs)?),
            ),
            ast::Expr::Unary(op, rhs) => {
                ExprKind::Unary(op.value().into(), Box::new(self.expr(rhs)?))
            }
            ast::Expr::Dot(lhs, _, rhs) => {
                ExprKind::Dot(Box::new(self.expr(lhs)?), rhs.str().to_owned())
            }
            ast::Expr::Cast(lhs, _, ty) => {
                ExprKind::Cast(Box::new(self.expr(lhs)?), self.gen_type(ty)?)
            }
            ast::Expr::Range(range) => {
                todo!()
                // ExprKind::Range(Box::new(self.expr(lhs)?), self.gen_type(ty)?)
            }
            ast::Expr::Ternary {
                condition,
                then_expr,
                else_expr,
                ..
            } => ExprKind::Ternary {
                condition: Box::new(self.expr(condition)?),
                then_expr: Box::new(self.expr(then_expr)?),
                else_expr: Box::new(self.expr(else_expr)?),
            },
            ast::Expr::Call {
                expr, arguments, ..
            } => {
                let arguments = arguments
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                if let ast::Expr::Dot(expr, _, fun_name) = expr.value() {
                    ExprKind::DotCall {
                        expr: Box::new(self.expr(expr)?),
                        field: fun_name.str().to_owned(),
                        arguments,
                    }
                } else {
                    ExprKind::Call {
                        expr: Box::new(self.expr(expr)?),
                        arguments,
                    }
                }
            }
            ast::Expr::Index { expr, index, .. } => ExprKind::Index {
                expr: Box::new(self.expr(expr)?),
                index: Box::new(self.expr(index)?),
            },
            ast::Expr::Array { members, .. } => {
                let members = members
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                ExprKind::Array { members }
            }
            ast::Expr::Struct {
                type_name, members, ..
            } => {
                let ty_name = self.gen_path_and_generics(type_name.value())?;
                let members = members
                    .iter()
                    .map(Spanned::value)
                    .map(|(name, expr)| Ok((name.str().to_owned(), Box::new(self.expr(expr)?))))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                ExprKind::Struct { ty_name, members }
            }
            ast::Expr::MacroCall(inner) => {
                if let Either::Right(expr) = inner.borrow().as_ref() {
                    return self.expr(expr);
                } else {
                    panic!("Unexpanded macro in ast lowering")
                }
            }
        };
        Ok(self.tir.mk_expr(expr_kind, expr.span.clone()))
    }

    fn pattern(&mut self, pattern: &Spanned<ast::Pattern>) -> Result<Pattern, ModGenError> {
        let pattern_kind = match pattern.value() {
            ast::Pattern::Variant(variant_name, lp, params, rp) => {
                let path = self.gen_path(variant_name.value())?;
                let params = params
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                let span = lp + rp;
                let pattern = Box::new(Pattern(span, PatternKind::Tuple(params)));
                PatternKind::Variant(path, pattern)
            }
            ast::Pattern::Tuple(_, members, _) => {
                let members = members
                    .iter()
                    .map(|pattern| self.pattern(pattern))
                    .collect::<Result<Vec<_>, ModGenError>>()?;
                PatternKind::Tuple(members)
            }
            ast::Pattern::Ident(name) => {
                if let ast::Name::Ident(name, tys) = name.value() {
                    assert!(tys.is_empty());
                    PatternKind::Ident(name.str().to_owned())
                } else {
                    panic!()
                }
            }
        };
        Ok(Pattern(pattern.span.clone(), pattern_kind))
    }
}
