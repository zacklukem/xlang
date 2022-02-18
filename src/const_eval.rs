use crate::ast;

#[derive(Debug)]
pub struct ConstEvaluator {}

impl ConstEvaluator {
    pub fn eval_usize(&self, expr: &ast::Expr) -> usize {
        match expr {
            ast::Expr::Integer(val, _) => usize::from_str_radix(val.str(), 10).unwrap(),
            _ => todo!("Support complex const literals"),
        }
    }
}
