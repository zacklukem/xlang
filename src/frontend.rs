use crate::macro_expansion;
use crate::{ast, codegen, error_context as ec, ir, mod_gen, monomorphize, parser, ty};
use clap::Parser;
use std::collections::HashMap;
use std::fs;
use std::path;

/// Compiles xlang source files
#[derive(Parser, Debug)]
#[clap(version, about, long_about = None)]
struct Args {
    /// The path to where to output the .c and .h files
    ///
    /// This should not include a file extension as .c and .h will be appended
    /// to this path to get the output file.
    #[clap(short)]
    output_file: String,

    /// The path to the standard library
    #[clap(long)]
    stl: Option<String>,

    /// The paths to the input files
    #[clap(short, required = true)]
    input_files: Vec<String>,
}

impl Args {
    pub fn output_file(&self) -> &str {
        &self.output_file
    }

    pub fn stl(&self) -> Option<&str> {
        self.stl.as_deref()
    }

    pub fn input_files(&self) -> &[String] {
        &self.input_files
    }
}

pub fn run() {
    let args = Args::parse();

    let tyc = ty::TyCtxContainer::new();
    let mut module = ir::Module::new(tyc.ctx());
    let mut err = ec::ErrorContext::default();

    if let Some(stl) = args.stl() {
        compile_stl(stl, &mut module, &mut err);
    }

    {
        let mut generators = Vec::new();

        for file in args.input_files() {
            generators.push(get_mod(file, &mut err));
        }

        gen_ir_on(&mut module, &mut err, &mut generators);
    }

    // Monomorphize
    let mut mono = monomorphize::Monomorphize::new(&module);
    mono.run();

    let (monos, special_types) = mono.finish();

    let header_filename = args.output_file().to_string() + ".h";
    let source_filename = args.output_file().to_string() + ".c";

    let header = std::fs::File::create(header_filename).unwrap();
    let source = std::fs::File::create(source_filename).unwrap();

    let mut header = std::io::BufWriter::new(header);
    let mut source = std::io::BufWriter::new(source);

    let mut codegen =
        codegen::CodeGen::new(&module, &monos, &special_types, &mut header, &mut source);
    codegen.gen(args.output_file()).unwrap();
}

fn parse_source<P: AsRef<path::Path>>(filename: P, err: &mut ec::ErrorContext) -> ast::Module {
    let filename_str = filename.as_ref().to_str().unwrap().to_owned();
    let source_string = std::fs::read_to_string(filename).unwrap();
    let source = std::rc::Rc::new(ast::Source::new(filename_str, source_string));

    let ast_module = parser::ModuleParser::new().parse(&source, &source.source_string[..]);
    let ast_module = match ast_module {
        Err(lalrpop_util::ParseError::UnrecognizedToken {
            token: (start, token, end),
            expected,
        }) => {
            let expected = expected.join(" | ");
            let msg = format!(r#"Got: "{token}". Expected: [{expected}]"#);
            source.print_msg((start, end), &msg, "Error");
            std::process::exit(1)
        }
        Err(e) => {
            println!("{:#?}", e);
            std::process::exit(1)
        }
        Ok(ast_module) => ast_module,
    };
    macro_expansion::expand_macros(&ast_module, err);
    ast_module
}

fn get_mod<'mg, 'ast, 'ty, P: AsRef<path::Path>>(
    file: P,
    err: &mut ec::ErrorContext,
) -> (ast::Module, String, HashMap<String, ir::Path>) {
    let file_name: String = {
        let file_name = file.as_ref().file_name().unwrap();
        file_name.to_str().unwrap().into()
    };
    let mod_name = &file_name[..file_name.len() - 3];
    let ast_module = parse_source(file, err);

    (ast_module, mod_name.into(), HashMap::new())
}

fn gen_ir_on<'ty>(
    module: &mut ir::Module<'ty>,
    err: &mut ec::ErrorContext,
    generators: &mut [(ast::Module, String, HashMap<String, ir::Path>)],
) {
    for (ast_module, mod_name, usages) in generators.iter_mut() {
        let mut mod_gen = mod_gen::ModGen::new(
            module,
            err,
            ast_module,
            ir::Path::Terminal(mod_name.clone()),
            usages,
        );

        if let Err(_) = mod_gen.declare_all() {
            print_pass_errors_and_exit(err);
            std::process::exit(1);
        }
        print_pass_errors_and_exit(err);
    }
    for (ast_module, mod_name, usages) in generators.iter_mut() {
        let mut mod_gen = mod_gen::ModGen::new(
            module,
            err,
            ast_module,
            ir::Path::Terminal(mod_name.clone()),
            usages,
        );
        if let Err(_) = mod_gen.define_all() {
            print_pass_errors_and_exit(err);
            std::process::exit(1);
        }
        print_pass_errors_and_exit(err);
    }
    for (ast_module, mod_name, usages) in generators.iter_mut() {
        let mut mod_gen = mod_gen::ModGen::new(
            module,
            err,
            ast_module,
            ir::Path::Terminal(mod_name.clone()),
            usages,
        );
        if let Err(_) = mod_gen.gen_all() {
            print_pass_errors_and_exit(err);
            std::process::exit(1);
        }
        print_pass_errors_and_exit(err);
    }
}

fn compile_stl<'ty>(stl: &str, module: &mut ir::Module<'ty>, err: &mut ec::ErrorContext) {
    let dirent = fs::read_dir(stl).unwrap();
    let mut mod_generators = Vec::new();
    for entry in dirent {
        let entry = entry.unwrap();
        let file = entry.path();
        if let Some(ext) = file.extension() {
            if ext == "xl" {
                mod_generators.push(get_mod(file, err));
            }
        }
    }
    gen_ir_on(module, err, &mut mod_generators);
}

fn print_pass_errors_and_exit(err: &ec::ErrorContext) {
    if err.has_errors() {
        err.print_all();
        std::process::exit(1);
    }
}
