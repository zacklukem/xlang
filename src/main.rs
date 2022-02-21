#[macro_use]
extern crate lalrpop_util;

pub mod ast;
pub mod const_eval;
pub mod error_context;
pub mod ir;
pub mod ir_display;
pub mod ir_gen;
pub mod mod_gen;
pub mod symbol;

lalrpop_mod!(pub parser);

fn main() {
    // let ty = parser::TypeParser::new()
    //     .parse("**mut [2() + a([3,4,5], true) * (&mut asdf - &mut 6)](i32, i64)")
    //     .unwrap();
    // println!("{:#?}", ty);

    let source_string = r#"
        struct Word {
            a: *Word,
            b: i64,
        }

        fun eat_i32(v: i32) {

        }

        fun Word::free(*self, v: i8, m: *[]i64) -> i32 {
            let k = 8 + 2;
            let (a,(b,c)) = (k, (8, 9));
            Word::free(self, 0, m);
            self.free(2, m);
            eat_i32(v);
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

    let mut mod_gen = mod_gen::ModGen::new(&mut module, &mut err, &ast_module);
    mod_gen.run().unwrap();

    println!("{:#?}", module);

    // println!("{:#?}", module);
}
