use crate::ast::{
    self, Expr, Ident, IntegerSpecifier, MacroCall, Module, Name, Source, Span, SpanBox, Spanned,
    Stmt, TopStmt,
};
use crate::error_context::ErrorContext;
use either::Either;
use std::cell::RefCell;
use std::rc::Rc;

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
            let span = &macro_call.name;
            let (line, col) = macro_call.name.line_col();
            let file_name = &macro_call.name.source.file_name;
            assert!(macro_call.arguments.len() == 0 || macro_call.arguments.len() == 1);
            *cell.borrow_mut() = Either::Right(Box::new(spanned(
                span,
                Expr::Call {
                    expr: Box::new(make_ast_ident(span, &["check", "panic_raw"])),
                    left_paren: macro_call.left_paren,
                    arguments: vec![
                        macro_call
                            .arguments
                            .get(0)
                            .cloned()
                            .unwrap_or_else(|| make_ast_string(span, "Explicit panic")),
                        make_ast_string(span, &format!(r"{file_name}:{line}:{col}")),
                    ],
                    right_paren: macro_call.right_paren,
                },
            )));
        } else if macro_call.name.str() == "@check" {
            let span = &macro_call.name;
            let (line, col) = macro_call.name.line_col();
            let file_name = &macro_call.name.source.file_name;

            assert!(macro_call.arguments.len() == 1 || macro_call.arguments.len() == 2);
            *cell.borrow_mut() = Either::Right(Box::new(spanned(
                span,
                Expr::Call {
                    expr: Box::new(make_ast_ident(span, &["check", "assert_raw"])),
                    left_paren: macro_call.left_paren,
                    arguments: vec![
                        macro_call.arguments[0].clone(),
                        macro_call
                            .arguments
                            .get(1)
                            .cloned()
                            .unwrap_or_else(|| make_ast_string(span, "Assertion failed")),
                        make_ast_string(span, &format!(r"{file_name}:{line}:{col}")),
                    ],
                    right_paren: macro_call.right_paren,
                },
            )));
        }
    }
}

fn spanned<T>(span: &Span, value: T) -> Spanned<T> {
    Spanned {
        value,
        span: span.clone(),
    }
}

fn make_ast_ident(span: &Span, path: &[&str]) -> Spanned<Expr> {
    spanned(span, Expr::Ident(make_ast_name(span, path)))
}

fn make_ast_string(span: &Span, s: &str) -> Spanned<Expr> {
    spanned(
        span,
        Expr::String(Span::from_macro_str(&format!(r#""{}""#, s), span)),
    )
}

fn make_ast_name(span: &Span, path: &[&str]) -> Name {
    assert!(!path.is_empty());
    let mut iter = path.iter().rev();
    let mut out = Name::Ident(
        Ident::from_macro_str(iter.next().unwrap(), span),
        Vec::new(),
    );
    for segment in iter {
        out = Name::Namespace(
            Ident::from_macro_str(segment, span),
            Vec::new(),
            span.clone(),
            Box::new(Spanned {
                value: out,
                span: span.clone(),
            }),
        )
    }
    out
}
