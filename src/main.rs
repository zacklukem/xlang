#[macro_use]
extern crate lalrpop_util;

extern crate clap;

pub mod ast;
pub mod codegen;
pub mod const_eval;
pub mod error_context;
pub mod frontend;
pub mod generics;
pub mod intern;
pub mod ir;
pub mod ir_display;
pub mod ir_gen;
pub mod mod_gen;
pub mod monomorphize;
pub mod ty;
pub mod ty_mangle;

lalrpop_mod!(#[allow(clippy::all)] pub parser);

fn main() {
    frontend::run();
}
