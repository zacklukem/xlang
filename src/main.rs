#[macro_use]
extern crate lalrpop_util;
extern crate clap;
extern crate either;

pub mod ast;
pub mod codegen;
pub mod const_eval;
pub mod error_context;
pub mod frontend;
pub mod generics;
pub mod infer;
pub mod intern;
pub mod ir;
pub mod ir_gen;
pub mod lexer;
pub mod macro_expansion;
pub mod mod_gen;
pub mod monomorphize;
pub mod tir;
pub mod tir_lower;
pub mod ty;
pub mod ty_mangle;

lalrpop_mod!(#[allow(clippy::all)] pub parser);

fn main() {
    env_logger::init();
    let start = std::time::Instant::now();
    frontend::run();
    let end = start.elapsed();
    println!("\n{:.3}s", end.as_secs_f32());
}
