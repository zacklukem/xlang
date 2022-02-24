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
pub mod ty_mangle;

lalrpop_mod!(pub parser);

fn print_pass_errors_and_exit(err: &error_context::ErrorContext) {
    if err.has_errors() {
        err.print_all();
        std::process::exit(1);
    }
}

fn main() {
    let mut args = std::env::args();

    args.next();
    let first_arg = args.next().unwrap();

    let source_string = std::fs::read_to_string(first_arg).unwrap();

    let source = std::rc::Rc::new(ast::Source::new(source_string));

    let ast_module = parser::ModuleParser::new().parse(&source, &source.source_string[..]);

    let ast_module = match ast_module {
        Err(lalrpop_util::ParseError::UnrecognizedToken {
            token: (start, token, end),
            expected,
        }) => {
            let expected = expected.join(" | ");
            let msg = format!(r#"Got: "{}". Expected: [{}]"#, token, expected);
            source.print_msg((start, end), &msg, "Error");
            std::process::exit(1)
        }
        Err(e) => {
            println!("{:#?}", e);
            std::process::exit(1)
        }
        Ok(ast_module) => ast_module,
    };

    let tyc = ty::TyCtxContainer::new();

    let module = ir::Module::new(tyc.ctx());

    let err = error_context::ErrorContext::new();

    let mut mod_gen = mod_gen::ModGen::new(module, err, &ast_module);
    mod_gen.run().unwrap();
    let (module, err) = mod_gen.finish();
    print_pass_errors_and_exit(&err);

    println!("{:?}", module.ty_ctx);

    println!("{:#?}", module.functions);
}
