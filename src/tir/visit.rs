use super::*;

impl<'ty> Stmt<'ty> {
    pub fn visit<S, E>(&self, mut s: S, e: E)
    where
        S: FnMut(&Stmt<'ty>) + Clone,
        E: FnMut(&Expr<'ty>) + Clone,
    {
        match self.kind() {
            StmtKind::If {
                condition,
                block,
                else_block,
            } => {
                condition.visit(e.clone());
                block.visit(s.clone(), e.clone());
                if let Some(else_block) = else_block {
                    else_block.visit(s.clone(), e);
                }
            }
            StmtKind::While {
                condition, block, ..
            } => {
                condition.visit(e.clone());
                block.visit(s.clone(), e);
            }
            StmtKind::Loop { block, .. } => block.visit(s.clone(), e),

            StmtKind::Case { expr, arms } => {
                expr.visit(e.clone());
                for arm in arms {
                    for stmt in &arm.stmts {
                        stmt.visit(s.clone(), e.clone());
                    }
                }
            }
            StmtKind::ForRange { range, block, .. } => {
                range.visit(e.clone());
                block.visit(s.clone(), e);
            }

            StmtKind::Block(stmts) => {
                for stmt in stmts {
                    stmt.visit(s.clone(), e.clone());
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
    pub fn visit<F>(&self, mut f: F)
    where
        F: FnMut(&Expr<'ty>) + Clone,
    {
        match self.kind() {
            ExprKind::Array { members: exprs } | ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    expr.visit(f.clone());
                }
            }

            ExprKind::Index {
                expr: lhs,
                index: rhs,
            }
            | ExprKind::Range(Range::Full(lhs, rhs))
            | ExprKind::Assign(lhs, _, rhs)
            | ExprKind::Binary(lhs, _, rhs) => {
                lhs.visit(f.clone());
                rhs.visit(f.clone());
            }
            ExprKind::Unary(_, expr)
            | ExprKind::Dot(expr, _)
            | ExprKind::Range(Range::Start(expr))
            | ExprKind::Range(Range::End(expr))
            | ExprKind::Cast(expr, _) => expr.visit(f.clone()),
            ExprKind::Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                condition.visit(f.clone());
                then_expr.visit(f.clone());
                else_expr.visit(f.clone());
            }
            ExprKind::Call { expr, arguments }
            | ExprKind::DotCall {
                expr, arguments, ..
            } => {
                expr.visit(f.clone());
                for expr in arguments {
                    expr.visit(f.clone());
                }
            }
            ExprKind::Struct { members, .. } => {
                for (_, expr) in members {
                    expr.visit(f.clone());
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
