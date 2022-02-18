#[macro_use]
extern crate lalrpop_util;

pub mod ast;
pub mod const_eval;
pub mod error_context;
pub mod ir;
pub mod ir_gen;
pub mod symbol;
pub mod type_check;

lalrpop_mod!(pub parser);

fn main() {
    // let ty = parser::TypeParser::new()
    //     .parse("**mut [2() + a([3,4,5], true) * (&mut asdf - &mut 6)](i32, i64)")
    //     .unwrap();
    // println!("{:#?}", ty);

    let source_string = r#"
        struct Word {
            a: *Word,
            b: *Word,
        }

        fun Word::free(*self, a: fun(i32) -> i32) -> i32 {
            let (a, b) = (1, 2);
        }
    "#;

    let source = std::rc::Rc::new(ast::Source {
        source_string: String::from(source_string),
    });

    let ast_module = parser::ModuleParser::new()
        .parse(&source, source_string)
        .unwrap();

    let mut module = ir::Module::new();

    let mut err = error_context::ErrorContext {};

    let mut checker = type_check::TypeChecker::new(&mut module, &mut err, &ast_module);
    checker.run().unwrap();

    println!("{:#?}", module);

    // println!("{:#?}", module);
}
