use super::*;
use crate::ty;

impl<'ty> Module<'ty> {
    /// Creates a new expression for variable access
    pub fn mk_var_expr(&self, varname: String, span: Span, ty: Ty<'ty>) -> Expr<'ty> {
        self.mk_expr(ExprKind::Ident(varname), span, ty)
    }

    /// Creates a new assignment expression using the lhs span and the type of lhs
    pub fn mk_assign_expr(&self, lhs: Expr<'ty>, op: AssignOp, rhs: Expr<'ty>) -> Expr<'ty> {
        let span = lhs.span().clone();
        let ty = self.ty_of(&lhs);
        self.mk_expr(ExprKind::Assign(Box::new(lhs), op, Box::new(rhs)), span, ty)
    }

    /// Creates a new expression and sets the type
    pub fn mk_expr(&self, kind: ExprKind<'ty>, span: Span, ty: Ty<'ty>) -> Expr<'ty> {
        let expr = Expr {
            kind,
            span,
            id: self.get_expr_id(),
        };
        self.set_ty(&expr, ty);
        expr
    }

    /// Create a constant usize literal
    pub fn mk_const_usize(&self, val: usize, span: Span) -> Expr<'ty> {
        let usize_ty = ty::primitive_ty(self.ty_ctx(), ty::PrimitiveType::USize);
        self.mk_expr(
            ExprKind::Integer(IntegerSpecifier::USize(val)),
            span.clone(),
            usize_ty,
        )
    }

    /// Create a boolean literal
    pub fn mk_const_bool(&self, val: bool, span: Span) -> Expr<'ty> {
        let bool_ty = ty::bool_ty(self.ty_ctx());
        self.mk_expr(ExprKind::Bool(val), span.clone(), bool_ty)
    }
}
