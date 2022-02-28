//! Handles printing and storing errors emitted by the compiler

use crate::ast;

#[derive(Debug)]
struct Error {
    kind: MsgKind,
    msg: String,
    span: ast::Span,
}

#[derive(Debug, Default)]
pub struct ErrorContext {
    errors: Vec<Error>,
}

#[derive(Debug)]
pub enum MsgKind {
    Error,
    Warning,
    Info,
}

impl ErrorContext {
    pub fn print_all(&self) {
        for error in &self.errors {
            error
                .span
                .print_msg(&error.msg, &format!("{:?}", error.kind));
        }
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn emit(&mut self, kind: MsgKind, msg: String, span: &ast::Span) {
        let span = span.clone();
        self.errors.push(Error { kind, msg, span });
        panic!()
    }

    pub fn err(&mut self, msg: String, span: &ast::Span) {
        self.emit(MsgKind::Error, msg, span);
    }
}
