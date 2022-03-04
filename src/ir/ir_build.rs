use super::*;
use crate::ty;

impl<'ty> Module<'ty> {
    pub fn mk_assign_expr(&self, lhs: Expr<'ty>, op: AssignOp, rhs: Expr<'ty>) -> Expr<'ty> {
        let span = lhs.span().clone();
        let ty = self.ty_of(&lhs);
        self.mk_expr(ExprKind::Assign(Box::new(lhs), op, Box::new(rhs)), span, ty)
    }

    pub fn mk_expr(&self, kind: ExprKind<'ty>, span: Span, ty: Ty<'ty>) -> Expr<'ty> {
        let expr = Expr {
            kind,
            span,
            fun_pass: None,
            id: self.get_expr_id(),
        };
        self.set_ty(&expr, ty);
        expr
    }

    pub fn mk_expr_pass(
        &self,
        kind: ExprKind<'ty>,
        span: Span,
        ty: Ty<'ty>,
        fun_pass: Box<Expr<'ty>>,
    ) -> Expr<'ty> {
        let expr = Expr {
            kind,
            span,
            fun_pass: Some(fun_pass),
            id: self.get_expr_id(),
        };
        self.set_ty(&expr, ty);
        expr
    }

    // pub fn mk_lhs_expr(&self, expr: Expr<'ty>) -> Expr<'ty> {
    //     let span = expr.span.clone();
    //     let ty = self.ty_of(&expr).mut_ptr(self.ty_ctx);
    //     self.mk_ty_expr(ExprKind::LhsExpr(Box::new(expr)), span, ty)
    // }

    pub fn mk_const_usize(&self, val: usize, span: Span) -> Expr<'ty> {
        let usize_ty = ty::primitive_ty(self.ty_ctx(), ty::PrimitiveType::USize);
        self.mk_expr(
            ExprKind::Integer(IntegerSpecifier::USize(val)),
            span.clone(),
            usize_ty,
        )
    }

    pub fn mk_const_bool(&self, val: bool, span: Span) -> Expr<'ty> {
        let bool_ty = ty::bool_ty(self.ty_ctx());
        self.mk_expr(ExprKind::Bool(val), span.clone(), bool_ty)
    }
}
