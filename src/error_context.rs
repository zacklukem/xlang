use crate::ast;

pub struct ErrorContext {}

pub enum MsgKind {
    Error,
    Warning,
    Info,
}

impl ErrorContext {
    pub fn emit(&mut self, kind: MsgKind, msg: String, span: &ast::Span) {
        println!("ERROR: {} {:?}", msg, span);
        panic!();
    }

    pub fn err(&mut self, msg: String, span: &ast::Span) {
        println!("ERROR: {} {:?}", msg, span);
        panic!();
    }
}
