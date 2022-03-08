use super::*;

impl<'ty> Stmt<'ty> {
    pub fn visit<S, E>(&self, s: &mut S, e: &mut E)
    where
        S: FnMut(&Stmt<'ty>),
        E: FnMut(&Expr<'ty>),
    {
        match self.kind() {
            StmtKind::If {
                condition,
                block,
                else_block,
            } => {
                condition.visit(e);
                block.visit(s, e);
                if let Some(else_block) = else_block {
                    else_block.visit(s, e);
                }
            }
            StmtKind::While {
                condition, block, ..
            } => {
                condition.visit(e);
                block.visit(s, e);
            }
            StmtKind::Loop { block, .. } => block.visit(s, e),

            StmtKind::Case { expr, arms } => {
                expr.visit(e);
                for arm in arms {
                    for stmt in &arm.stmts {
                        stmt.visit(s, e);
                    }
                }
            }
            StmtKind::ForRange { range, block, .. } => {
                range.visit(e);
                block.visit(s, e);
            }

            StmtKind::Block(stmts) => {
                for stmt in stmts {
                    stmt.visit(s, e);
                }
            }

            StmtKind::Let { expr, .. } | StmtKind::Return(Some(expr)) | StmtKind::Expr(expr) => {
                expr.visit(e)
            }

            StmtKind::InlineC { .. }
            | StmtKind::Return(None)
            | StmtKind::Continue(_)
            | StmtKind::Break(_) => (),
        }
        s(self);
    }
}

impl<'ty> Expr<'ty> {
    pub fn visit<F>(&self, f: &mut F)
    where
        F: FnMut(&Expr<'ty>),
    {
        match self.kind() {
            ExprKind::Array { members: exprs } | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    expr.visit(f);
                }
            }

            ExprKind::Index {
                expr: lhs,
                index: rhs,
            }
            | ExprKind::Range(Range::Full(lhs, rhs))
            | ExprKind::Assign(lhs, _, rhs)
            | ExprKind::Binary(lhs, _, rhs) => {
                lhs.visit(f);
                rhs.visit(f);
            }
            ExprKind::Unary(_, expr)
            | ExprKind::Dot(expr, _)
            | ExprKind::Range(Range::Start(expr))
            | ExprKind::Range(Range::End(expr))
            | ExprKind::Cast(expr, _) => expr.visit(f),
            ExprKind::Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                condition.visit(f);
                then_expr.visit(f);
                else_expr.visit(f);
            }
            ExprKind::Call { expr, arguments }
            | ExprKind::DotCall {
                expr, arguments, ..
            } => {
                expr.visit(f);
                for expr in arguments {
                    expr.visit(f);
                }
            }
            ExprKind::Struct { members, .. } => {
                for (_, expr) in members {
                    expr.visit(f);
                }
            }
            ExprKind::Range(Range::All)
            | ExprKind::Ident(..)
            | ExprKind::Integer(..)
            | ExprKind::Float(..)
            | ExprKind::String(..)
            | ExprKind::Bool(..)
            | ExprKind::Null => (),
        }
        f(self);
    }
}
