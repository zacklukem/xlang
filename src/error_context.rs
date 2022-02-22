use crate::ast;

pub struct ErrorContext {}

pub enum MsgKind {
    Error,
    Warning,
    Info,
}

impl ErrorContext {
    pub fn emit(&mut self, _kind: MsgKind, msg: String, span: &ast::Span) {
        span.print_msg(&msg);
        panic!();
    }

    pub fn err(&mut self, msg: String, span: &ast::Span) {
        span.print_msg(&msg);
        panic!();
    }
}
