//! For evaluation constant values such as the size of array types.
//!
//! Currently only parses single usize integers

use crate::ast;

#[derive(Debug)]
pub struct ConstEvaluator {}

impl ConstEvaluator {
    pub fn eval_usize(&self, expr: &ast::Expr) -> usize {
        match expr {
            ast::Expr::Integer(val, _) => val.str().parse::<usize>().unwrap(),
            _ => todo!("Support complex const literals"),
        }
    }
}
