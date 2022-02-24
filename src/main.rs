#[macro_use]
extern crate lalrpop_util;

pub mod ast;
pub mod const_eval;
pub mod error_context;
pub mod intern;
pub mod ir;
pub mod ir_display;
pub mod ir_gen;
pub mod mod_gen;
pub mod ty;

lalrpop_mod!(pub parser);

fn main() {
    // let ty = parser::TypeParser::new()
    //     .parse("**mut [2() + a([3,4,5], true) * (&mut asdf - &mut 6)](i32, i64)")
    //     .unwrap();
    // println!("{:#?}", ty);

    let source_string = include_str!("../linked_list.x");

    let source = std::rc::Rc::new(ast::Source::new(String::from(source_string)));

    let ast_module = parser::ModuleParser::new().parse(&source, source_string);

    let ast_module = match ast_module {
        Err(lalrpop_util::ParseError::UnrecognizedToken {
            token: (start, token, end),
            expected,
        }) => {
            let expected = expected.join(" | ");
            let msg = format!(r#"Got: "{}". Expected: [{}]"#, token, expected);
            source.print_msg((start, end), &msg);
            return;
        }
        Err(e) => {
            println!("{:#?}", e);
            return;
        }
        Ok(ast_module) => ast_module,
    };

    let tyc = ty::TyCtxContainer::new();

    let module = ir::Module::new(tyc.ctx());

    let err = error_context::ErrorContext {};

    let mut mod_gen = mod_gen::ModGen::new(module, err, &ast_module);
    mod_gen.run().unwrap();
    let (module, _err) = mod_gen.finish();

    // println!("TyCtx: {:#?}", module.ty_ctx);

    println!("{:#?}", module.functions);
}
