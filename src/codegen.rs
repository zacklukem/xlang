use crate::generics::replace_generics;
use crate::intern::Int;
use crate::ir::{
    AssignOp, BinOp, DefKind, Expr, ExprKind, ExternKind, FloatSpecifier, IntegerSpecifier, Module,
    Path, Stmt, StmtKind, UnaryOp,
};
use crate::monomorphize::DefInstance;
use crate::ty::{AdtType, PrimitiveType, Ty, TyKind};
use crate::ty_mangle::mangle_ty_vec;
use std::collections::HashSet;
use std::fmt::Result as FmtResult;
use std::fmt::Write as FmtWrite;
use std::io::Result as IoResult;
use std::io::Write;

#[derive(Debug)]
pub struct CodeGen<'ty, T> {
    module: &'ty Module<'ty>,
    monos: &'ty HashSet<DefInstance<'ty>>,
    special_types: &'ty HashSet<Ty<'ty>>,
    header_writer: &'ty mut T,
    source_writer: &'ty mut T,
    indent: usize,
}

pub fn mangle_path(path: &Path) -> String {
    let mut st = String::new();
    write_mangle_path(path, &mut st).unwrap();
    st
}

fn write_mangle_path<T>(path: &Path, f: &mut T) -> FmtResult
where
    T: FmtWrite,
{
    match path {
        Path::Terminal(val) => f.write_str(val),
        Path::Namespace(namespace, next) => {
            f.write_str(namespace)?;
            f.write_str("_")?;
            write_mangle_path(next, f)
        }
    }
}

fn zip_clone_vec<T, U>(left: &[T], right: &[U]) -> Vec<(T, U)>
where
    T: Clone,
    U: Clone,
{
    assert_eq!(left.len(), right.len());
    left.iter().cloned().zip(right.iter().cloned()).collect()
}

fn primitive_c_ty(pt: &PrimitiveType) -> &'static str {
    use PrimitiveType::*;
    match pt {
        Void => "void",
        Bool => "bool",
        F64 => "double",
        F32 => "float",
        I64 => "int64_t",
        I32 => "int32_t",
        I16 => "int16_t",
        I8 => "int8_t",
        USize => "size_t",
        U64 => "uint64_t",
        U32 => "uint32_t",
        U16 => "uint16_t",
        U8 => "uint8_t",
        Integer => panic!(),
    }
}

impl<'ty> Ty<'ty> {
    pub fn to_c_type(self, ident: Option<&str>) -> String {
        let mut out = String::new();
        self.to_c_type_write(ident, &mut out).unwrap();
        out
    }

    pub fn to_c_type_write<T>(self, ident: Option<&str>, f: &mut T) -> FmtResult
    where
        T: FmtWrite,
    {
        use TyKind::*;
        match self.0 .0 {
            Primitive(pt) => {
                f.write_str(primitive_c_ty(pt))?;
                if let Some(ident) = ident {
                    f.write_str(" ")?;
                    f.write_str(ident)?;
                }
            }
            Param(_ty_param) => panic!("Unexpected type param"),
            Pointer(_, Ty(Int(SizedArray(_size, _inner)))) => {
                todo!()
            }
            Pointer(_, Ty(Int(UnsizedArray(inner)))) => {
                f.write_str("slice_t(")?;
                inner.to_c_type_write(None, f)?;
                f.write_str(")")?;
                if let Some(ident) = ident {
                    f.write_str(" ")?;
                    f.write_str(ident)?;
                }
            }
            Pointer(_, inner) => {
                inner.to_c_type_write(None, f)?;
                f.write_str(" *")?;
                if let Some(ident) = ident {
                    f.write_str(ident)?;
                }
            }
            Tuple(types) => {
                write!(f, "tuple")?;
                for ty in types {
                    f.write_str("_")?;
                    ty.mangle_write(f)?;
                }
                f.write_str("_t")?;
                if let Some(ident) = ident {
                    f.write_str(" ")?;
                    f.write_str(ident)?;
                }
            }
            // ret (*name)(params,..)
            Fun(params, ret) => {
                assert!(ident.is_some());
                ret.to_c_type_write(None, f)?;
                write!(f, " (*{})(", ident.unwrap())?;
                for (i, ty) in params.iter().enumerate() {
                    ty.to_c_type_write(None, f)?;
                    if i + 1 < params.len() {
                        f.write_str(", ")?;
                    }
                }
                f.write_str(")")?;
            }
            SizedArray(_size, _inner) => {
                todo!()
            }
            UnsizedArray(_inner) => {
                todo!()
            }
            Range(_inner) => {
                todo!()
            }
            Lhs(inner) => inner.to_c_type_write(ident, f)?,
            Adt(AdtType {
                def_id: _,
                path,
                ty_params,
            }) => {
                write!(f, "{}", mangle_path(path))?;
                for ty in ty_params {
                    f.write_str("_")?;
                    ty.mangle_write(f)?;
                }
                f.write_str("_t")?;
                if let Some(ident) = ident {
                    f.write_str(" ")?;
                    f.write_str(ident)?;
                }
            }
            Err => f.write_str("ERR_TY")?,
            Unknown => f.write_str("ERR_TY")?,
        }
        Ok(())
    }
}

impl<'ty, T> CodeGen<'ty, T>
where
    T: Write,
{
    pub fn new(
        module: &'ty Module<'ty>,
        monos: &'ty HashSet<DefInstance<'ty>>,
        special_types: &'ty HashSet<Ty<'ty>>,
        header_writer: &'ty mut T,
        source_writer: &'ty mut T,
    ) -> CodeGen<'ty, T> {
        CodeGen {
            indent: 0,
            module,
            monos,
            special_types,
            header_writer,
            source_writer,
        }
    }

    pub fn gen(&mut self, path: &str) -> IoResult<()> {
        writeln!(self.header_writer, "#pragma once")?;
        writeln!(self.header_writer, "#include <xlang/default_header.h>")?;
        self.output_predefined()?;
        self.output_struct_defs()?;

        let path = std::path::Path::new(path);
        let filename = path.file_name().unwrap().to_str().unwrap();

        writeln!(self.source_writer, r#"#include "{}.h""#, filename)?;

        self.output_funs()?;

        Ok(())
    }

    fn output_predefined(&mut self) -> IoResult<()> {
        writeln!(self.header_writer)?;

        for ty in self.special_types {
            if let TyKind::Tuple(tys) = ty.0 .0 {
                let mangle = ty.to_c_type(None);
                writeln!(self.header_writer, "#ifndef XLANG_DECLARE_{}", mangle)?;
                writeln!(self.header_writer, "#define XLANG_DECLARE_{}", mangle)?;
                write!(self.header_writer, "typedef struct ")?;

                write!(self.header_writer, "tuple")?;
                for ty in tys {
                    let mangle = ty.mangle();
                    write!(self.header_writer, "_{}", mangle)?;
                }
                writeln!(self.header_writer, " {};", mangle)?;

                writeln!(self.header_writer, "#endif")?;
            }
        }

        writeln!(self.header_writer)?;

        for (def_id, def) in self.module.defs_iter() {
            if let DefKind::Enum { variants, .. } = &def.kind {
                let path = self.module.get_path_by_def_id(*def_id);
                let path = mangle_path(path);
                let path_name = path.clone() + "_k";
                writeln!(self.header_writer, "enum {0} {{", path_name)?;
                for variant in variants.keys() {
                    writeln!(self.header_writer, "    {}_{}_k,", path.clone(), variant)?;
                }
                writeln!(self.header_writer, "}};")?;
            }
        }

        for mono in self.monos {
            let def = self.module.get_def_by_id(mono.def_id);
            let path = self.module.get_path_by_def_id(mono.def_id);
            match &def.kind {
                DefKind::Struct { .. } => {
                    let path_name = mangle_path(path) + &mangle_ty_vec(&mono.ty_params);
                    writeln!(self.header_writer, "typedef struct {0} {0}_t;", path_name)?;
                }
                DefKind::Enum { .. } => {
                    let path_name = mangle_path(path) + &mangle_ty_vec(&mono.ty_params);
                    writeln!(self.header_writer, "typedef struct {0} {0}_t;", path_name)?;
                }
                _ => (),
            }
        }

        writeln!(self.header_writer)?;

        for mono in self.monos {
            let def = self.module.get_def_by_id(mono.def_id);
            let path = self.module.get_path_by_def_id(mono.def_id);
            if let DefKind::Fun {
                ty_params,
                params,
                return_type,
                ..
            } = &def.kind
            {
                let fun_name = mangle_path(path) + &mangle_ty_vec(&mono.ty_params);

                let generics = zip_clone_vec(ty_params, &mono.ty_params);
                let return_type = replace_generics(self.module.ty_ctx(), *return_type, &generics);
                let return_type = return_type.to_c_type(None);
                write!(self.header_writer, "{} {}(", return_type, fun_name)?;
                for (i, (name, param)) in params.iter().enumerate() {
                    let param = replace_generics(self.module.ty_ctx(), *param, &generics);
                    write!(self.header_writer, "{}", param.to_c_type(Some(name)))?;
                    if i + 1 < params.len() {
                        write!(self.header_writer, ", ")?;
                    }
                }
                writeln!(self.header_writer, ");")?;
            }
        }

        for ty in self.special_types {
            if let TyKind::Tuple(tys) = ty.0 .0 {
                let mangle = ty.to_c_type(None);
                writeln!(self.header_writer, "#ifndef XLANG_DEFINE_{}", mangle)?;
                writeln!(self.header_writer, "#define XLANG_DEFINE_{}", mangle)?;
                write!(self.header_writer, "struct ")?;

                write!(self.header_writer, "tuple")?;
                for ty in tys {
                    let mangle = ty.mangle();
                    write!(self.header_writer, "_{}", mangle)?;
                }
                writeln!(self.header_writer, " {{")?;
                for (i, ty) in tys.iter().enumerate() {
                    let ident = format!("_{}", i);
                    let def = ty.to_c_type(Some(&ident));
                    writeln!(self.header_writer, "    {};", def)?;
                }
                writeln!(self.header_writer, "}};")?;

                writeln!(self.header_writer, "#endif")?;
            }
        }

        Ok(())
    }

    fn output_struct_defs(&mut self) -> IoResult<()> {
        for mono in self.monos {
            let def = self.module.get_def_by_id(mono.def_id);
            let path = self.module.get_path_by_def_id(mono.def_id);
            match &def.kind {
                DefKind::Struct {
                    members, ty_params, ..
                } => {
                    let path_name = mangle_path(path) + &mangle_ty_vec(&mono.ty_params);

                    let generics = zip_clone_vec(ty_params, &mono.ty_params);

                    writeln!(self.header_writer, "\nstruct {0} {{", path_name)?;
                    for (name, ty) in members {
                        let ty = replace_generics(self.module.ty_ctx(), *ty, &generics);
                        let ty = ty.to_c_type(Some(name));
                        writeln!(self.header_writer, "    {};", ty)?;
                    }
                    writeln!(self.header_writer, "}};")?;
                }
                DefKind::Enum {
                    variants,
                    ty_params,
                    ..
                } => {
                    let path = mangle_path(path);
                    let path_name = path.clone() + &mangle_ty_vec(&mono.ty_params);
                    let kind_type_name = path.clone() + "_k";

                    let generics = zip_clone_vec(ty_params, &mono.ty_params);

                    writeln!(self.header_writer, "\nstruct {0} {{", path_name)?;
                    writeln!(self.header_writer, "    enum {} kind;", kind_type_name)?;
                    writeln!(self.header_writer, "    union {{")?;
                    for (name, ty) in variants {
                        let ty = replace_generics(self.module.ty_ctx(), *ty, &generics);
                        let ty = ty.to_c_type(Some(name));
                        writeln!(self.header_writer, "        {};", ty)?;
                    }
                    writeln!(self.header_writer, "    }};")?;
                    writeln!(self.header_writer, "}};")?;
                }
                _ => (),
            }
        }

        Ok(())
    }

    fn output_funs(&mut self) -> IoResult<()> {
        for mono in self.monos {
            let def = self.module.get_def_by_id(mono.def_id);
            let path = self.module.get_path_by_def_id(mono.def_id);
            match &def.kind {
                DefKind::Fun {
                    ty_params,
                    params,
                    return_type,
                    external,
                } if matches!(
                    external,
                    ExternKind::Define | ExternKind::VariantConstructor
                ) =>
                {
                    let fun_name = mangle_path(path) + &mangle_ty_vec(&mono.ty_params);

                    let generics = zip_clone_vec(ty_params, &mono.ty_params);
                    let return_type =
                        replace_generics(self.module.ty_ctx(), *return_type, &generics);
                    let return_type = return_type.to_c_type(None);
                    write!(self.source_writer, "{} {}(", return_type, fun_name)?;
                    for (i, (name, param)) in params.iter().enumerate() {
                        let param = replace_generics(self.module.ty_ctx(), *param, &generics);
                        write!(self.source_writer, "{}", param.to_c_type(Some(name)))?;
                        if i + 1 < params.len() {
                            write!(self.source_writer, ", ")?;
                        }
                    }
                    writeln!(self.source_writer, ") {{")?;
                    if *external == ExternKind::Define {
                        let fun = self.module.functions.get(&mono.def_id).unwrap();

                        for (name, ty) in &fun.variable_defs {
                            let ty = replace_generics(self.module.ty_ctx(), *ty, &generics);
                            let ty = ty.to_c_type(Some(name));
                            writeln!(self.source_writer, "    {};", ty)?;
                        }

                        self.stmt(&fun.block, &generics)?;
                    } else {
                        let variant = path.end();
                        let enum_name = path.pop_end().unwrap();
                        let variants = if let DefKind::Enum { variants, .. } =
                            &self.module.get_def_by_path(&enum_name).unwrap().kind
                        {
                            variants
                        } else {
                            panic!()
                        };
                        let inner_ty = variants.get(variant).unwrap();
                        let inner_ty = replace_generics(self.module.ty_ctx(), *inner_ty, &generics);
                        let inner_ty = inner_ty.to_c_type(None);

                        let mut initializers = String::new();
                        for i in 0..params.len() {
                            initializers += &format!("_{}", i);
                            if i < params.len() - 1 {
                                initializers += ", ";
                            }
                        }

                        let kind = mangle_path(path);
                        // let inner_ty =
                        writeln!(
                            self.source_writer,
                            "    {return_type} out;\n    \
                             out.kind = {kind}_k;\n    \
                             out.{variant} = ({inner_ty}){{ {initializers} }};\n    \
                             return out;",
                        )?;
                    }
                    writeln!(self.source_writer, "}}")?;
                }
                _ => (),
            }
        }

        Ok(())
    }

    pub fn stmt(&mut self, stmt: &Stmt<'ty>, ty_params: &[(String, Ty<'ty>)]) -> IoResult<()> {
        use StmtKind::*;
        macro_rules! indent {
            () => {
                for _ in 0..self.indent {
                    write!(self.f(), "    ")?;
                }
            };
        }
        match &stmt.kind {
            If {
                condition,
                block,
                else_block,
            } => {
                write!(self.source_writer, "if (")?;
                self.expr(condition, ty_params)?;
                write!(self.source_writer, ")")?;
                self.stmt(block, ty_params)?;
                if let Some(else_block) = else_block {
                    write!(self.source_writer, " else ")?;
                    self.stmt(else_block, ty_params)?;
                }
            }
            While { condition, block } => {
                write!(self.source_writer, "while (")?;
                self.expr(condition, ty_params)?;
                write!(self.source_writer, ")")?;
                self.stmt(block, ty_params)?;
            }
            For {
                initializer: _,
                condition: _,
                incrementor: _,
                block: _,
            } => {
                todo!()
            }
            Labeled(label, stmt) => {
                writeln!(self.source_writer, "{}:", label)?;
                if let Some(stmt) = stmt {
                    indent!();
                    self.stmt(stmt, ty_params)?;
                }
            }
            Block(stmts) => {
                writeln!(self.source_writer, "{{")?;
                self.indent += 1;
                for stmt in stmts {
                    indent!();
                    self.stmt(stmt, ty_params)?;
                    writeln!(self.source_writer)?;
                }
                self.indent -= 1;
                indent!();
                write!(self.source_writer, "}}")?;
            }
            StmtList(stmts) => {
                for stmt in stmts {
                    indent!();
                    self.stmt(stmt, ty_params)?;
                    writeln!(self.source_writer)?;
                }
            }
            Return(expr) => {
                write!(self.source_writer, "return ")?;
                if let Some(expr) = expr {
                    self.expr(expr, ty_params)?;
                }
                write!(self.source_writer, ";")?;
            }
            Goto(label) => {
                write!(self.source_writer, "goto {};", label)?;
            }
            Expr(expr) => {
                self.expr(expr, ty_params)?;
                write!(self.source_writer, ";")?;
            }
            Switch {
                expr,
                cases,
                default,
            } => {
                write!(self.source_writer, "switch (")?;
                self.expr(expr, ty_params)?;
                writeln!(self.source_writer, ") {{")?;
                for (expr, stmt) in cases {
                    write!(self.source_writer, "case ")?;
                    self.expr(expr, ty_params)?;
                    writeln!(self.source_writer, ":")?;
                    self.stmt(stmt, ty_params)?;
                    writeln!(self.source_writer, "break;")?;
                }
                if let Some(stmt) = default {
                    writeln!(self.source_writer, "default:")?;
                    self.stmt(stmt, ty_params)?;
                    writeln!(self.source_writer, "break;")?;
                }
                write!(self.source_writer, "}}")?;
            }
        }
        Ok(())
    }

    pub fn f(&mut self) -> &mut T {
        self.source_writer
    }

    pub fn expr(&mut self, expr: &Expr<'ty>, ty_params: &[(String, Ty<'ty>)]) -> IoResult<()> {
        use ExprKind::*;
        match &expr.kind {
            Ident(id) => write!(self.f(), "{}", id)?,
            // HACK: make some system for intrinsics
            Call { expr, arguments }
                if arguments.is_empty()
                    && matches!(&expr.kind,
            GlobalIdent(Path::Namespace(ns, path), generics)
                if ns == "mem" && matches!(path.as_ref(), Path::Terminal(name) if name == "sizeof") && generics.len() == 1) =>
            {
                if let GlobalIdent(_, generics) = &expr.kind {
                    let ty = generics[0];
                    let ty = replace_generics(self.module.ty_ctx(), ty, ty_params);
                    let ty = ty.to_c_type(None);
                    write!(self.f(), "sizeof({})", ty)?;
                } else {
                    panic!()
                }
            }
            GlobalIdent(path, generics) => {
                let generics = generics
                    .iter()
                    .map(|ty| replace_generics(self.module.ty_ctx(), *ty, ty_params))
                    .collect::<Vec<_>>();
                let path_name = mangle_path(path) + &mangle_ty_vec(&generics);
                write!(self.f(), "{}", path_name)?;
            }
            Integer(spec) => write!(self.f(), "{}", spec.to_c())?,
            Float(spec) => write!(self.f(), "{}", spec.to_c())?,
            // TODO: escape
            String(st) => write!(self.f(), r#"{}"#, st)?,
            Bool(true) => write!(self.f(), "true")?,
            Bool(false) => write!(self.f(), "false")?,
            Null => write!(self.f(), "XLANG_NULL")?,
            LhsExpr(expr) => self.expr(expr, ty_params)?,
            Tuple(tys) => {
                write!(self.f(), "(")?;
                for (i, arg) in tys.iter().enumerate() {
                    self.expr(arg, ty_params)?;
                    if i + 1 < tys.len() {
                        write!(self.f(), ", ")?;
                    }
                }
                write!(self.f(), ")")?;
            }
            Assign(lhs, op, rhs) => {
                write!(self.f(), "(")?;
                self.expr(lhs, ty_params)?;
                write!(self.f(), "{}", op.to_c())?;
                self.expr(rhs, ty_params)?;
                write!(self.f(), ")")?;
            }
            Binary(lhs, BinOp::EqEq, rhs) => {
                self.expr(lhs, ty_params)?;
                write!(self.f(), "==")?;
                self.expr(rhs, ty_params)?;
            }
            Binary(lhs, op, rhs) => {
                write!(self.f(), "(")?;
                self.expr(lhs, ty_params)?;
                write!(self.f(), "{}", op.to_c())?;
                self.expr(rhs, ty_params)?;
                write!(self.f(), ")")?;
            }
            Unary(UnaryOp::Box, rhs) => {
                let inner_ty = rhs.ty();
                let inner_ty = replace_generics(self.module.ty_ctx(), inner_ty, ty_params);
                let inner_ty = inner_ty.to_c_type(None);

                let ptr_name = "__ptr";

                write!(
                    self.f(),
                    "({{{0} *{1} = malloc(sizeof({0})); *{1} = ",
                    inner_ty,
                    ptr_name,
                )?;
                self.expr(rhs, ty_params)?;
                write!(self.f(), "; {};}})", ptr_name)?;
                // write!(self.f(), "&")?;
                // self.expr(rhs, ty_params)?;
                // write!(self.f(), ")")?;
            }
            Unary(op, rhs) => {
                write!(self.f(), "(")?;
                write!(self.f(), "{}", op.to_c())?;
                self.expr(rhs, ty_params)?;
                write!(self.f(), ")")?;
            }
            // Just for fun :)
            Dot(lhs, member) if matches!(&lhs.kind, Unary(UnaryOp::Deref, _)) => {
                if let Unary(UnaryOp::Deref, lhs) = &lhs.kind {
                    self.expr(lhs, ty_params)?;
                    write!(self.f(), "->{}", member)?;
                }
            }
            Dot(lhs, member) => {
                self.expr(lhs, ty_params)?;
                write!(self.f(), ".{}", member)?;
            }
            Cast(expr, ty) => {
                if !ty.is_integer_ukn() {
                    let ty = replace_generics(self.module.ty_ctx(), *ty, ty_params);
                    let ty = ty.to_c_type(None);
                    write!(self.f(), "({})(", ty)?;
                    self.expr(expr, ty_params)?;
                    write!(self.f(), ")")?;
                } else {
                    self.expr(expr, ty_params)?;
                }
            }
            Range(_from, _to) => todo!(),
            RangeFrom(_to) => todo!(),
            Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                write!(self.f(), "((")?;
                self.expr(condition, ty_params)?;
                write!(self.f(), ") ? (")?;
                self.expr(then_expr, ty_params)?;
                write!(self.f(), ") : (")?;
                self.expr(else_expr, ty_params)?;
                write!(self.f(), "))")?;
            }
            Call { expr, arguments } => {
                self.expr(expr, ty_params)?;
                write!(self.f(), "(")?;
                for (i, arg) in arguments.iter().enumerate() {
                    self.expr(arg, ty_params)?;
                    if i + 1 < arguments.len() {
                        write!(self.f(), ", ")?;
                    }
                }
                write!(self.f(), ")")?;
            }
            Index { expr, index } => {
                self.expr(expr, ty_params)?;
                write!(self.f(), "[")?;
                self.expr(index, ty_params)?;
                write!(self.f(), "]")?;
            }
            Array { members: _ } => todo!(),
            Struct { ty, members } => {
                //todo
                let ty = replace_generics(self.module.ty_ctx(), *ty, ty_params);
                let ct = ty.to_c_type(None);
                write!(self.f(), "(({}){{", ct)?;
                for (i, (name, value)) in members.iter().enumerate() {
                    write!(self.f(), ".{} = ", name)?;
                    self.expr(value, ty_params)?;
                    if i + 1 < members.len() {
                        write!(self.f(), ", ")?;
                    }
                }
                write!(self.f(), "}})")?;
            }
            Err => todo!(),
        }
        Ok(())
    }
}

impl FloatSpecifier {
    fn to_c(&self) -> String {
        use FloatSpecifier::*;
        match self {
            F32(val) => format!("{}f", val),
            F64(val) => format!("{}", val),
        }
    }
}

impl IntegerSpecifier {
    fn to_c(&self) -> String {
        use IntegerSpecifier::*;
        match self {
            I8(val) => format!("{}", val),
            I16(val) => format!("{}", val),
            I32(val) => format!("{}", val),
            I64(val) => format!("{}", val),
            U8(val) => format!("{}", val),
            U16(val) => format!("{}", val),
            U32(val) => format!("{}", val),
            U64(val) => format!("{}", val),
            USize(val) => format!("{}", val),
            Signed(val) => format!("{}", val),
            Unsigned(val) => format!("{}", val),
        }
    }
}

impl AssignOp {
    fn to_c(&self) -> &'static str {
        match self {
            AssignOp::Eq => "=",
            AssignOp::AddEq => "+=",
            AssignOp::SubEq => "-=",
            AssignOp::MulEq => "*=",
            AssignOp::DivEq => "/=",
            AssignOp::ModEq => "%=",
            AssignOp::XorEq => "^=",
            AssignOp::AndEq => "&=",
            AssignOp::OrEq => "|=",
        }
    }
}

impl BinOp {
    fn to_c(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Xor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::And => "&",
            BinOp::Or => "|",
            BinOp::AndAnd => "&&",
            BinOp::OrOr => "||",
            BinOp::Lt => "<",
            BinOp::Gt => ">",
            BinOp::LtEq => "<=",
            BinOp::GtEq => ">=",
            BinOp::EqEq => "==",
            BinOp::NotEq => "!=",
        }
    }
}

impl UnaryOp {
    fn to_c(&self) -> &'static str {
        match self {
            UnaryOp::Neg => "-",
            UnaryOp::LogNot => "!",
            UnaryOp::BitNot => "~",
            UnaryOp::Deref => "*",
            UnaryOp::Ref => "&",
            UnaryOp::RefMut => "&",
            UnaryOp::Box => panic!("cannot be directly converted"),
        }
    }
}
