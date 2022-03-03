//! Generates modules

use crate::ast::{self, TopStmt};
use crate::error_context::ErrorContext;
use crate::ir;
use crate::ir_gen;
use crate::ty;
use std::collections::hash_map;
use std::collections::HashMap;

pub struct ModGen<'mg, 'ast, 'ty> {
    ast_module: &'ast ast::Module,
    module: &'mg mut ir::Module<'ty>,
    err: &'mg mut ErrorContext,
    current_generics: Vec<String>,
    mod_path: ir::Path,
    usages: &'mg mut HashMap<String, ir::Path>,
}

#[derive(Debug)]
pub enum ModGenError {
    UnableToDeclare,
}

pub trait TypeGenerator<'ast, 'ty> {
    fn current_generics(&self) -> &[String];
    fn module(&self) -> &ir::Module<'ty>;
    fn mod_path(&self) -> &ir::Path;
    fn usages(&self) -> &HashMap<String, ir::Path>;
    fn err(&mut self) -> &mut ErrorContext;

    fn gen_type(&mut self, ty: &ast::Spanned<ast::Type>) -> Result<ty::Ty<'ty>, ModGenError> {
        let ty = match ty.value() {
            ast::Type::Primitive(pt) => ty::primitive_ty(self.module().ty_ctx(), pt.value().into()),
            ast::Type::Named(name) => {
                let (path, ty_params) = self.gen_path_and_generics(name.value())?;
                match path {
                    ir::Path::Terminal(st) if self.current_generics().contains(&st) => {
                        self.module().ty_ctx().int(ty::TyKind::Param(st))
                    }
                    _ => {
                        if let Some(def_id) = self.module().get_def_id_by_path(&path) {
                            self.module().ty_ctx().int(ty::TyKind::Adt(ty::AdtType {
                                def_id,
                                path,
                                ty_params,
                            }))
                        } else {
                            self.err().err("Type name not found".into(), &ty.span);
                            ty::err_ty(self.module().ty_ctx())
                        }
                    }
                }
            }
            ast::Type::Pointer(kind, ty) => self.module().ty_ctx().int(ty::TyKind::Pointer(
                kind.value().into(),
                self.gen_type(ty.as_ref())?,
            )),
            ast::Type::Tuple(_, tys, _) => self
                .module()
                .ty_ctx()
                .int(ty::TyKind::Tuple(self.gen_type_iter(tys.iter())?)),
            ast::Type::Fun(params, ret) => self.module().ty_ctx().int(ty::TyKind::Fun(
                self.gen_type_iter(params.iter())?,
                match ret {
                    Some(ret) => self.gen_type(ret)?,
                    None => ty::void_ty(self.module().ty_ctx()),
                },
            )),
            ast::Type::SizedArray {
                size, inner_type, ..
            } => self.module().ty_ctx().int(ty::TyKind::SizedArray(
                self.module().const_eval().eval_usize(size.value()),
                self.gen_type(inner_type)?,
            )),
            ast::Type::UnsizedArray { inner_type, .. } => self
                .module()
                .ty_ctx()
                .int(ty::TyKind::UnsizedArray(self.gen_type(inner_type)?)),
        };
        Ok(ty)
    }

    fn gen_type_iter<'a, T>(&mut self, iter: T) -> Result<Vec<ty::Ty<'ty>>, ModGenError>
    where
        T: std::iter::Iterator<Item = &'a ast::Spanned<ast::Type>>,
    {
        let mut out = Vec::with_capacity(iter.size_hint().0);
        for ty in iter {
            out.push(self.gen_type(ty)?);
        }
        Ok(out)
    }

    fn gen_path(&self, name: &ast::Name) -> Result<ir::Path, ModGenError> {
        let path = self.gen_path_rec(name)?;
        let first = path.first();
        if let Some(usage) = self.usages().get(first) {
            Ok(usage.append(path))
        } else {
            Ok(path)
        }
    }

    fn gen_path_rec(&self, name: &ast::Name) -> Result<ir::Path, ModGenError> {
        match name {
            ast::Name::Ident(id, _) => Ok(ir::Path::Terminal(id.str().into())),
            ast::Name::Namespace(id, _, _, next) => {
                let next = self.gen_path_rec(next.value())?;
                Ok(ir::Path::Namespace(id.str().into(), Box::new(next)))
            }
        }
    }

    fn gen_path_and_generics(
        &mut self,
        name: &ast::Name,
    ) -> Result<(ir::Path, Vec<ty::Ty<'ty>>), ModGenError> {
        let (path, generics) = self.gen_path_and_generics_rec(name)?;
        let first = path.first();
        if let Some(usage) = self.usages().get(first) {
            Ok((usage.append(path), generics))
        } else {
            Ok((path, generics))
        }
    }

    fn gen_path_and_generics_rec(
        &mut self,
        name: &ast::Name,
    ) -> Result<(ir::Path, Vec<ty::Ty<'ty>>), ModGenError> {
        match name {
            ast::Name::Ident(id, generics) => Ok((
                ir::Path::Terminal(id.str().into()),
                self.gen_type_iter(generics.iter())?,
            )),
            ast::Name::Namespace(id, _, _, next) => {
                let (next, generics) = self.gen_path_and_generics_rec(next.value())?;
                Ok((
                    ir::Path::Namespace(id.str().into(), Box::new(next)),
                    generics,
                ))
            }
        }
    }
}

impl<'mg, 'ast, 'ty> TypeGenerator<'ast, 'ty> for ModGen<'mg, 'ast, 'ty> {
    fn current_generics(&self) -> &[String] {
        &self.current_generics
    }

    fn module(&self) -> &ir::Module<'ty> {
        self.module
    }

    fn mod_path(&self) -> &ir::Path {
        &self.mod_path
    }

    fn usages(&self) -> &HashMap<String, ir::Path> {
        self.usages
    }

    fn err(&mut self) -> &mut ErrorContext {
        self.err
    }
}

impl<'mg, 'ast, 'ty> ModGen<'mg, 'ast, 'ty> {
    pub fn new(
        module: &'mg mut ir::Module<'ty>,
        err: &'mg mut ErrorContext,
        ast_module: &'ast ast::Module,
        mod_path: ir::Path,
        usages: &'mg mut HashMap<String, ir::Path>,
    ) -> ModGen<'mg, 'ast, 'ty> {
        ModGen {
            ast_module,
            module,
            err,
            mod_path,
            current_generics: Vec::new(),
            usages,
        }
    }

    fn gen_path_raw(&self, name: &'ast ast::Name) -> Result<ir::Path, ModGenError> {
        match name {
            ast::Name::Ident(id, _) => Ok(ir::Path::Terminal(id.str().into())),
            ast::Name::Namespace(id, _, _, next) => Ok(ir::Path::Namespace(
                id.str().into(),
                Box::new(self.gen_path_raw(next.value())?),
            )),
        }
    }

    fn gen_def_path(&mut self, name: &'ast ast::Name) -> Result<ir::Path, ModGenError> {
        let path = self.gen_path_raw(name)?;
        if let ir::Path::Terminal(name) = &path {
            if name == "main" {
                return Ok(path);
            }
        }

        let first = path.first().clone();

        let full_path = self.mod_path().append(path);

        if let hash_map::Entry::Vacant(e) = self.usages.entry(first) {
            e.insert(self.mod_path.clone());
        }

        Ok(full_path)
    }

    pub fn declare_all(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            if let TopStmt::Use(_, name) = stmt.value() {
                let path = self.gen_path_raw(name.value())?;
                let end = path.end();
                let head = path.pop_end().unwrap();
                self.usages.insert(end.clone(), head);
            }
        }
        let def = ir::Def::new(
            ir::DefVisibility::Public,
            ir::DefKind::Mod {
                symbols: Default::default(),
            },
        );
        self.module.declare(self.mod_path.clone(), def).unwrap();
        self.declare_types()?;
        Ok(())
    }

    pub fn define_all(&mut self) -> Result<(), ModGenError> {
        self.define_types()?;
        Ok(())
    }

    pub fn gen_all(&mut self) -> Result<(), ModGenError> {
        self.gen_ir()?;
        Ok(())
    }

    /// First pass, declare all struct types
    fn declare_types(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            let stmt = &stmt.value;
            match stmt {
                TopStmt::Enum {
                    pub_tok,
                    type_params,
                    name,
                    ..
                } => {
                    let path = self.gen_def_path(name.value())?;
                    let def = ir::Def::new(
                        if pub_tok.is_some() {
                            ir::DefVisibility::Public
                        } else {
                            ir::DefVisibility::Private
                        },
                        ir::DefKind::Enum {
                            symbols: Default::default(),
                            variants: Default::default(),
                            // TODO: insert these
                            ty_params: type_params.iter().map(|v| v.str().into()).collect(),
                        },
                    );
                    self.module.declare(path, def).unwrap();
                }
                TopStmt::Struct {
                    pub_tok,
                    type_params,
                    name,
                    ..
                } => {
                    let path = self.gen_def_path(name.value())?;
                    let def = ir::Def::new(
                        if pub_tok.is_some() {
                            ir::DefVisibility::Public
                        } else {
                            ir::DefVisibility::Private
                        },
                        ir::DefKind::Struct {
                            symbols: Default::default(),
                            members: Default::default(),
                            // TODO: insert these
                            ty_params: type_params.iter().map(|v| v.str().into()).collect(),
                        },
                    );
                    self.module.declare(path, def).unwrap();
                }
                // ignore other top level stmts
                _ => (),
            }
        }
        Ok(())
    }

    /// second pass, define all types (including function types)
    fn define_types(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            let stmt = &stmt.value;
            match stmt {
                // Define struct types
                TopStmt::Struct {
                    name,
                    type_params,
                    members,
                    ..
                } => self.define_struct(name, type_params, members)?,
                TopStmt::Enum {
                    name,
                    type_params,
                    variants,
                    ..
                } => self.define_enum(name, type_params, variants)?,
                TopStmt::FunDecl {
                    pub_tok,
                    type_params,
                    name,
                    params,
                    return_type,
                    ..
                } => self.define_fun_type(true, pub_tok, type_params, name, params, return_type)?,
                TopStmt::Fun {
                    pub_tok,
                    type_params,
                    name,
                    params,
                    return_type,
                    ..
                } => {
                    self.define_fun_type(false, pub_tok, type_params, name, params, return_type)?
                }
                _ => (),
            }
        }
        Ok(())
    }

    fn get_fun_self_type(
        &mut self,
        span: &ast::Span,
        struct_name: &ir::Path,
        struct_generics: Vec<ty::Ty<'ty>>,
    ) -> Option<ty::Ty<'ty>> {
        match self.module.get_def_by_path(struct_name) {
            Some(ir::Def {
                kind: ir::DefKind::Struct { .. },
                ..
            })
            | Some(ir::Def {
                kind: ir::DefKind::Enum { .. },
                ..
            }) => {
                let def_id = self.module.get_def_id_by_path(struct_name).unwrap();

                Some(
                    self.module
                        .ty_ctx()
                        .int(ty::TyKind::Adt(ty::AdtType {
                            def_id,
                            path: struct_name.clone(),
                            ty_params: struct_generics,
                        }))
                        .ptr(self.module.ty_ctx()),
                )
            }
            _ => {
                self.err.err(
                    "Functions with self type must be members of struct namespace".into(),
                    span,
                );
                None
            }
        }
    }

    /// Define a function type in second pass
    fn define_fun_type(
        &mut self,
        external: bool,
        pub_tok: &'ast Option<ast::Span>,
        type_params: &'ast [ast::Span],
        ast_fun_name: &'ast ast::Spanned<ast::Name>,
        (self_type, params): &'ast ast::FunParams,
        return_type: &'ast Option<ast::SpanBox<ast::Type>>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let fun_name = self.gen_def_path(ast_fun_name.value())?;
        let self_param: Option<ty::Ty<'ty>> = if self_type.is_some() {
            if fun_name.is_terminal() {
                self.err.err(
                    "Functions with self type must be members of struct namespace".into(),
                    &ast_fun_name.span,
                );
                None
            } else {
                let struct_name = ast_fun_name.value().pop_end().unwrap();
                let (struct_path, struct_generics) = self.gen_path_and_generics(&struct_name)?;
                self.get_fun_self_type(&ast_fun_name.span, &struct_path, struct_generics)
            }
        } else {
            None
        };
        let mut fun_params = if let Some(ty) = self_param {
            vec![(String::from("self"), ty)]
        } else {
            vec![]
        };

        let mut params_mapped = {
            let mut out = Vec::with_capacity(params.len());
            for ast::Spanned {
                value: (name, ty), ..
            } in params.iter()
            {
                out.push((
                    String::from(name.str()),
                    ModGen::<'mg, 'ast, 'ty>::gen_type(self, ty)?,
                ));
            }
            out
        };

        fun_params.append(&mut params_mapped);
        let visibility = if pub_tok.is_some() {
            ir::DefVisibility::Public
        } else {
            ir::DefVisibility::Private
        };
        let return_type = match return_type {
            Some(ty) => self.gen_type(ty)?,
            None => ty::void_ty(self.module.ty_ctx()),
        };
        let def = ir::DefKind::Fun {
            external: if external {
                ir::ExternKind::Declare
            } else {
                Default::default()
            },
            params: fun_params,
            return_type,
            // TODO: insert these
            ty_params: self.current_generics.clone(),
        };
        match self.module.declare(fun_name, ir::Def::new(visibility, def)) {
            Err(ir::DefineErr::AlreadyExists) => self
                .err()
                .err("This function already exists".into(), &ast_fun_name.span),
            Err(ir::DefineErr::DeclareOnFun) => self.err().err(
                "Functions cannot act as namespaces".into(),
                &ast_fun_name.span,
            ),
            Err(ir::DefineErr::NoModule) => self
                .err()
                .err("No such namespace exists".into(), &ast_fun_name.span),
            _ => (),
        }
        self.current_generics.clear();
        Ok(())
    }

    fn define_enum(
        &mut self,
        ast_enum_name: &'ast ast::Spanned<ast::Name>,
        type_params: &'ast [ast::Span],
        variants: &'ast ast::SpanSlice<(ast::Ident, ast::SpanVec<ast::Type>)>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let enum_path = self.gen_def_path(ast_enum_name.value())?;
        let def_id = self.module.get_def_id_by_path(&enum_path).unwrap();

        let fun_ty_params = self
            .current_generics
            .iter()
            .map(|name| self.module.ty_ctx().int(ty::TyKind::Param(name.clone())))
            .collect();

        let self_ty = ty::TyKind::Adt(ty::AdtType {
            def_id,
            path: enum_path.clone(),
            ty_params: fun_ty_params,
        });
        let self_ty = self.module.ty_ctx().int(self_ty);

        let mut sym_variants = HashMap::new();

        for spanned_variant in variants.iter() {
            let (variant_name, variant_types) = &spanned_variant.value;
            let types = self.gen_type_iter(variant_types.iter())?;

            let fun_params = types
                .iter()
                .enumerate()
                .map(|(i, ty)| (format!("_{}", i), *ty))
                .collect();

            let fun_name = enum_path.push_end(variant_name.str().into());

            let fun_def = ir::DefKind::Fun {
                external: ir::ExternKind::VariantConstructor,
                params: fun_params,
                return_type: self_ty,
                ty_params: self.current_generics.clone(),
            };

            self.module
                .declare(fun_name, ir::Def::new(ir::DefVisibility::Public, fun_def))
                .unwrap();

            let ty = ty::TyKind::Tuple(types);
            let ty = self.module.ty_ctx().int(ty);

            let name = variant_name.str().into();
            // if sym_variants.contains_key(&name) {
            //     self.err.err(
            //         format!(
            //             "The enum {:?} already contains a variant named {}",
            //             ast_enum_name.value, name
            //         ),
            //         &variant_name.span,
            //     )
            // } else {
            //     sym_variants.insert(name, ty);
            // }
            match sym_variants.entry(name) {
                hash_map::Entry::Vacant(e) => {
                    e.insert(ty);
                }
                hash_map::Entry::Occupied(e) => self.err.err(
                    format!(
                        "The enum {:?} already contains a variant named {}",
                        ast_enum_name.value,
                        e.key()
                    ),
                    &variant_name.span,
                ),
            }
        }

        let sym = self.module.get_mut_def_by_id(def_id);
        if let ir::DefKind::Enum { variants, .. } = &mut sym.kind {
            *variants = sym_variants;
        } else {
            panic!("Inconsistent define/declare passes");
        }
        self.current_generics.clear();
        Ok(())
    }

    /// Define a struct in second pass
    fn define_struct(
        &mut self,
        ast_struct_name: &'ast ast::Spanned<ast::Name>,
        type_params: &'ast [ast::Span],
        members: &'ast ast::SpanSlice<(ast::Ident, ast::SpanBox<ast::Type>)>,
    ) -> Result<(), ModGenError> {
        self.current_generics.clear();
        self.current_generics
            .extend(type_params.iter().map(|p| p.str().into()));
        let struct_path = self.gen_def_path(ast_struct_name.value())?;

        let mut sym_members = HashMap::new();

        for spanned_member in members.iter() {
            let (field_name, field_type) = &spanned_member.value;
            let ty = self.gen_type(field_type.as_ref())?;
            let name = field_name.str().into();
            match sym_members.entry(name) {
                hash_map::Entry::Vacant(e) => {
                    e.insert(ty);
                }
                hash_map::Entry::Occupied(e) => self.err.err(
                    format!(
                        "The struct {:?} already contains a member named {}",
                        ast_struct_name.value,
                        e.key()
                    ),
                    &field_name.span,
                ),
            }
        }

        let sym = self.module.get_mut_def_by_path(&struct_path).unwrap();
        if let ir::DefKind::Struct { members, .. } = &mut sym.kind {
            *members = sym_members;
        } else {
            panic!("Inconsistent define/declare passes");
        }
        self.current_generics.clear();
        Ok(())
    }

    fn gen_ir(&mut self) -> Result<(), ModGenError> {
        for stmt in &self.ast_module.top_stmts {
            if let ast::TopStmt::Fun { name, body, .. } = &stmt.value {
                let path = self.gen_path(name.value())?;
                self.gen_fun_ir(path, body)?;
            }
        }
        Ok(())
    }

    fn gen_fun_ir(
        &mut self,
        path: ir::Path,
        body: &'ast ast::SpanBox<ast::FunBlock>,
    ) -> Result<(), ModGenError> {
        let (params, return_type, generics) = if let ir::DefKind::Fun {
            params,
            return_type,
            ty_params,
            ..
        } =
            &self.module.get_def_by_path(&path).unwrap().kind
        {
            (params.clone(), *return_type, ty_params.clone())
        } else {
            unreachable!()
        };

        let def_id = self.module.get_def_id_by_path(&path).unwrap();

        let body = ir_gen::gen_fun_block(
            self.usages,
            self.module,
            format!("{}", path),
            self.err,
            def_id,
            params,
            return_type,
            body,
            generics,
        )?;

        self.module.functions.insert(def_id, body);

        Ok(())
    }
}
