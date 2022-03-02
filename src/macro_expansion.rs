use crate::ast::{
    self, Expr, Ident, MacroCall, Module, Name, Span, SpanBox, Spanned, Stmt, TopStmt,
};
use crate::error_context::ErrorContext;
use either::Either;
use std::cell::RefCell;

pub fn expand_macros(ast_module: &Module, err: &mut ErrorContext) {
    let mut exp = MacroExpander { ast_module, err };
    exp.expand_macros();
}

struct MacroExpander<'a> {
    ast_module: &'a Module,
    #[allow(dead_code)]
    err: &'a mut ErrorContext,
}

impl<'a> MacroExpander<'a> {
    fn expand_macros(&mut self) {
        for top_stmt in &self.ast_module.top_stmts {
            match &top_stmt.value {
                TopStmt::Fun { body, .. } => {
                    for stmt in &body.value.stmts {
                        self.expand_stmt(stmt);
                    }
                }
                _ => (),
            }
        }
    }

    fn expand_stmt(&mut self, stmt: &Spanned<Stmt>) {
        use Stmt::*;
        match &stmt.value {
            If {
                condition,
                block,
                else_block,
                ..
            } => {
                self.expand_expr(condition);
                self.expand_stmt(block);
                if let Some(else_block) = else_block {
                    self.expand_stmt(else_block);
                }
            }

            Loop { block, .. } => {
                self.expand_stmt(block);
            }

            Case { expr, arms, .. } => {
                self.expand_expr(expr);
                for arm in arms {
                    for stmt in &arm.value.stmts {
                        self.expand_stmt(stmt);
                    }
                }
            }

            While {
                condition: expr,
                block,
                ..
            }
            | ForRange {
                range: expr, block, ..
            } => {
                self.expand_expr(expr.as_ref());
                self.expand_stmt(block);
            }

            Block(_, stmts, _) => {
                for stmt in stmts {
                    self.expand_stmt(stmt);
                }
            }

            Let { expr, .. } | Return(_, Some(expr)) | Expr(expr) => {
                self.expand_expr(expr.as_ref());
            }

            InlineC { .. } | Return(_, None) | Continue(_, _) | Break(_, _) => (),
        }
    }

    fn expand_expr(&mut self, expr: &Spanned<Expr>) {
        use Expr::*;
        match expr.value() {
            Range(ast::Range::All(_))
            | Ident(_)
            | Integer(..)
            | Float(..)
            | String(_)
            | Bool(..)
            | Null(_) => (),

            Struct { members, .. } => {
                for Spanned {
                    value: (_, expr), ..
                } in members
                {
                    self.expand_expr(expr);
                }
            }

            Array { members: exprs, .. } | Tuple(_, exprs, _) => {
                for expr in exprs {
                    self.expand_expr(expr);
                }
            }

            Index {
                expr: lhs,
                index: rhs,
                ..
            }
            | Range(ast::Range::Full(lhs, _, rhs))
            | Assign(lhs, _, rhs)
            | Binary(lhs, _, rhs) => {
                self.expand_expr(lhs);
                self.expand_expr(rhs);
            }

            Range(ast::Range::Start(expr, _))
            | Range(ast::Range::End(_, expr))
            | Unary(_, expr)
            | Dot(expr, _, _)
            | Cast(expr, _, _) => self.expand_expr(expr),

            Ternary {
                condition,
                then_expr,
                else_expr,
                ..
            } => {
                self.expand_expr(condition);
                self.expand_expr(then_expr);
                self.expand_expr(else_expr);
            }

            // expr(index, ...)
            Call {
                expr, arguments, ..
            } => {
                self.expand_expr(expr);
                for expr in arguments {
                    self.expand_expr(expr);
                }
            }

            // expr[index]
            MacroCall(cell) => self.expand_macro_call(cell),
        }
    }

    fn expand_macro_call(&mut self, cell: &RefCell<Either<MacroCall, SpanBox<Expr>>>) {
        let macro_call = cell.borrow().clone().left().unwrap();
        if macro_call.name.str() == "@panic" {
            let (line, col) = macro_call.name.line_col();
            let source = macro_call.left_paren.source.clone();
            assert_eq!(macro_call.arguments.len(), 1);
            *cell.borrow_mut() = Either::Right(Box::new(Spanned {
                value: Expr::Call {
                    expr: Box::new(Spanned {
                        value: Expr::Ident(Name::Namespace(
                            Ident::from_macro_str(&source, "check"),
                            Vec::new(),
                            Span::from_macro_str(&source, "::"),
                            Box::new(Spanned {
                                value: Name::Ident(
                                    Ident::from_macro_str(&source, "panic"),
                                    Vec::new(),
                                ),
                                span: Span::from_macro_str(&source, "panic"),
                            }),
                        )),
                        span: Span::from_macro_str(&source, "check::panic"),
                    }),
                    left_paren: macro_call.left_paren,
                    arguments: vec![
                        macro_call.arguments[0].clone(),
                        Spanned {
                            value: Expr::String(Span::from_macro_str(
                                &source,
                                &format!(r#""{}:{}""#, line, col),
                            )),
                            span: Span::from_macro_str(&source, "<macro expand>"),
                        },
                    ],
                    right_paren: macro_call.right_paren,
                },
                span: Span::from_macro_str(&source, "<macro expand>"),
            }));
        }
    }
}
