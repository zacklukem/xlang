#[macro_use]
extern crate lalrpop_util;

pub mod ast;
pub mod codegen;
pub mod const_eval;
pub mod error_context;
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

fn print_pass_errors_and_exit(err: &error_context::ErrorContext) {
    if err.has_errors() {
        err.print_all();
        std::process::exit(1);
    }
}

fn main() {
    let tyc = ty::TyCtxContainer::new();

    let mut module = ir::Module::new(tyc.ctx());

    let mut err = error_context::ErrorContext::default();

    let mut args = std::env::args();

    args.next();
    let first_arg = args.next().unwrap();
    let second_arg = args.next().unwrap();

    let stl_members = ["stl/check.xl", "stl/mem.xl"];

    for member in stl_members {
        // Compile stl
        let source_string = std::fs::read_to_string(member).unwrap();
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

        let mod_name = &member[4..member.len() - 3];
        println!("{:?}", mod_name);

        // Gen module
        let mut mod_gen = mod_gen::ModGen::new(
            module,
            err,
            &ast_module,
            ir::Path::Terminal(mod_name.into()),
        );
        mod_gen.run().unwrap();
        (module, err) = mod_gen.finish();
        print_pass_errors_and_exit(&err);
    }

    {
        let source_string = std::fs::read_to_string(first_arg).unwrap();
        // Compile input file
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

        let mod_name = std::path::Path::new(&second_arg)
            .file_name()
            .unwrap()
            .to_str()
            .unwrap();
        // Gen module
        let mut mod_gen = mod_gen::ModGen::new(
            module,
            err,
            &ast_module,
            ir::Path::Terminal(mod_name.into()),
        );
        mod_gen.run().unwrap();
        (module, err) = mod_gen.finish();
        print_pass_errors_and_exit(&err);
    }

    // Monomorphize
    let mut mono = monomorphize::Monomorphize::new(&module);
    mono.run();

    let (monos, special_types) = mono.finish();

    let header_filename = second_arg.clone() + ".h";
    let source_filename = second_arg.clone() + ".c";

    let header = std::fs::File::create(header_filename).unwrap();
    let source = std::fs::File::create(source_filename).unwrap();
    let mut header = std::io::BufWriter::new(header);
    let mut source = std::io::BufWriter::new(source);

    let mut codegen =
        codegen::CodeGen::new(&module, &monos, &special_types, &mut header, &mut source);
    codegen.gen(&second_arg).unwrap();

    // println!("{:?}", module.ty_ctx);
}
