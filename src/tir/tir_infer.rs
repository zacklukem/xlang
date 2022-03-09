use std::collections::VecDeque;

use log::debug;

use super::*;
use crate::error_context::ErrorContext;
use crate::frontend::print_pass_errors_and_exit;
use crate::generics::replace_generics;

use crate::infer::solve::contains_ty_var;
use crate::infer::*;
use crate::intern::Int;
use crate::ir;
use crate::mod_gen::ModGenError;
use crate::ty::{self, AdtType, Ty, TyCtx, TyKind};

type InferResult<T> = Result<T, ModGenError>;

pub fn tir_infer<'ty>(
    md: &ir::Module<'ty>,
    tir: &mut TirCtx<'ty>,
    err: &mut ErrorContext,
    return_type: Ty<'ty>,
    params: &[(String, Ty<'ty>)],
    stmt: &Stmt<'ty>,
) -> InferResult<()> {
    let mut infer = TirInfer {
        md,
        tir,
        err,
        return_type,
        icx: InferCtx::new(md),
        tcx: md.ty_ctx(),
        scope: Box::new(Scope::from_params(params)),
    };
    infer.stmt(stmt)?;
    infer.solve(stmt)?;

    Ok(())
}

struct TirInfer<'a, 'ty> {
    md: &'a ir::Module<'ty>,
    tir: &'a mut TirCtx<'ty>,
    err: &'a mut ErrorContext,
    return_type: Ty<'ty>,
    icx: InferCtx<'a, 'ty>,
    tcx: TyCtx<'ty>,
    scope: Box<Scope<'ty>>,
}

impl<'a, 'ty> TirInfer<'a, 'ty> {
    fn in_scope<R, F>(&mut self, f: F) -> R
    where
        F: FnOnce(&mut Self) -> R,
    {
        let old_scope = std::mem::take(&mut self.scope);
        self.scope.parent = Some(old_scope);
        let r = f(self);
        let parent = std::mem::take(&mut self.scope.parent);
        self.scope = parent.unwrap();
        r
    }

    pub fn stmt(&mut self, stmt: &Stmt<'ty>) -> InferResult<()> {
        use StmtKind::*;
        match stmt.kind() {
            If {
                condition,
                block,
                else_block,
            } => {
                let condition_ty = self.expr(condition)?;
                let bool_ty = ty::bool_ty(self.tcx);
                self.icx
                    .eq(condition_ty, bool_ty)
                    .emit(self.err, condition.span())
                    .ok();
                self.stmt(block)?;
                if let Some(else_block) = else_block {
                    self.stmt(else_block)?;
                }
            }
            While {
                condition, block, ..
            } => {
                let condition_ty = self.expr(condition)?;
                let bool_ty = ty::bool_ty(self.tcx);
                self.icx
                    .eq(condition_ty, bool_ty)
                    .emit(self.err, condition.span())
                    .ok();
                self.stmt(block)?;
            }
            Loop { block, .. } => {
                self.stmt(block)?;
            }
            Case { expr, arms } => {
                let expr_ty = self.expr(expr)?;

                // Setup generic args from first arm
                // This is a hack, because the first arm isn't always a variant arm
                let (generics, _variant_path) = if let Some(arm) = arms.first() {
                    if let PatternKind::Variant(path, _) = &arm.pattern.1 {
                        let def = self.md.get_def_by_path(path);
                        if let Some(ir::DefKind::Fun {
                            ty_params,
                            return_type,
                            ..
                        }) = def.map(ir::Def::kind)
                        {
                            let generics = ty_params
                                .iter()
                                .map(|ty_params| (ty_params.clone(), self.icx.mk_var()))
                                .collect::<Vec<_>>();
                            let variant_ty = replace_generics(self.tcx, *return_type, &generics);
                            let variant_path =
                                if let TyKind::Adt(AdtType { path, .. }) = variant_ty.0 .0 {
                                    path
                                } else {
                                    todo!()
                                };

                            self.icx
                                .eq(variant_ty, expr_ty)
                                .emit(self.err, expr.span())
                                .ok();

                            (generics, variant_path)
                        } else {
                            todo!()
                        }
                    } else {
                        todo!()
                    }
                } else {
                    todo!()
                };

                // Actually gen the arms
                for arm in arms {
                    if let PatternKind::Variant(path, inner_pattern) = &arm.pattern.1 {
                        let def = self.md.get_def_by_path(path);
                        if let Some(ir::DefKind::Fun {
                            params,
                            return_type: _,
                            ..
                        }) = def.map(ir::Def::kind)
                        {
                            self.in_scope(|this| {
                                let param_tys = params
                                    .iter()
                                    .map(|(_, ty)| replace_generics(this.tcx, *ty, &generics));

                                if let PatternKind::Tuple(patterns) = &inner_pattern.1 {
                                    assert_eq!(params.len(), patterns.len());
                                    for (pat, ty) in patterns.iter().zip(param_tys) {
                                        if let PatternKind::Ident(id) = &pat.1 {
                                            this.scope.insert(id.clone(), ty);
                                        }
                                    }
                                } else {
                                    todo!()
                                }
                                for stmt in &arm.stmts {
                                    this.stmt(stmt)?;
                                }
                                Ok(())
                            })?;
                        } else {
                            todo!()
                        }
                    } else {
                        todo!("{:?}", arm)
                    }
                }
            }
            ForRange {
                label: _,
                initializer: _,
                range: _,
                block: _,
            } => {
                // TODO
                todo!()
            }
            Let {
                pattern,
                type_name,
                expr,
                ..
            } => {
                if let Pattern(_, PatternKind::Ident(var_name)) = pattern.as_ref() {
                    let expr_ty = self.expr(expr)?;
                    let ty = if let Some(type_name) = type_name {
                        *type_name
                    } else {
                        expr_ty
                    };
                    self.scope.insert(var_name.clone(), ty);
                    // self.icx.eq(expr_ty, ty).emit(self.err, expr.span()).ok();
                } else {
                    todo!()
                }
            }
            Block(stmts) => self.in_scope(|this| {
                for stmt in stmts {
                    this.stmt(stmt)?;
                }
                Ok(())
            })?,
            Return(Some(expr)) => {
                let expr_ty = self.expr(expr)?;
                self.icx
                    .eq(expr_ty, self.return_type)
                    .emit(self.err, stmt.span())
                    .ok();
            }
            Expr(expr) => {
                self.expr(expr)?;
            }
            Return(None) | InlineC { .. } | Continue(..) | Break(..) => (),
        }
        Ok(())
    }

    fn gen_ident(&mut self, span: &Span, path: &Path, ty_args: &RefCell<Vec<Ty<'ty>>>) -> Ty<'ty> {
        // First see if the ident is in scope as a local variable
        if let Path::Terminal(id) = &path {
            if let Some(ty) = self.scope.resolve(&id) {
                return ty;
            }
        }
        // Otherwise check for values in namespace
        if let Some(ir::Def {
            kind:
                ir::DefKind::Fun {
                    ty_params,
                    params,
                    return_type,
                    ..
                },
            ..
        }) = self.md.get_def_by_path(path)
        {
            let mut ty_args = ty_args.borrow_mut();
            if !ty_args.is_empty() && ty_args.len() != ty_params.len() {
                self.err.err("Invalid type params".to_owned(), span);
                return ty::err_ty(self.tcx);
            }
            if ty_args.is_empty() {
                *ty_args = ty_params.iter().map(|_| self.icx.mk_var()).collect()
            }
            let generics: Vec<_> = ty_params
                .iter()
                .cloned()
                .zip(ty_args.iter().copied())
                .collect();

            let ty = TyKind::Fun(params.iter().map(|(_, ty)| *ty).collect(), *return_type);
            let ty = self.tcx.int(ty);
            replace_generics(self.tcx, ty, &generics)
        } else {
            self.err.err("Name not found in scope".to_owned(), span);
            ty::err_ty(self.tcx)
        }
    }

    pub fn expr(&mut self, expr: &Expr<'ty>) -> InferResult<Ty<'ty>> {
        use ExprKind::{
            Array, Assign, Binary, Bool, Call, Cast, Dot, DotCall, Float, Ident, Index, Integer,
            Null, Range, String as StringExpr, Struct, Ternary, Tuple, Unary,
        };
        let ty = match expr.kind() {
            Ident(path, ty_args) => self.gen_ident(expr.span(), path, ty_args),
            Null => ty::void_ty(self.tcx).ptr(self.tcx),

            Tuple(exprs) => {
                let tys = exprs
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<InferResult<Vec<_>>>()?;
                self.tcx.int(TyKind::Tuple(tys))
            }

            Assign(lhs, _, rhs) => {
                let lhs_ty = self.expr(lhs)?;
                let rhs_ty = self.expr(rhs)?;
                self.icx.eq(lhs_ty, rhs_ty).emit(self.err, expr.span()).ok();
                lhs_ty
            }

            Binary(lhs, op, rhs) => {
                let lhs_ty = self.expr(lhs)?;
                let rhs_ty = self.expr(rhs)?;
                match op {
                    // Numerical
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::Xor
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::And
                    | BinOp::Or => {
                        // TODO: assert numeric
                        self.icx.eq(lhs_ty, rhs_ty).emit(self.err, expr.span()).ok();
                        lhs_ty
                    }
                    // Logical
                    BinOp::AndAnd | BinOp::OrOr => {
                        let bool_ty = ty::bool_ty(self.tcx);
                        self.icx.eq(lhs_ty, bool_ty).emit(self.err, lhs.span()).ok();
                        self.icx.eq(rhs_ty, bool_ty).emit(self.err, rhs.span()).ok();
                        bool_ty
                    }
                    // Comparison
                    BinOp::Lt
                    | BinOp::Gt
                    | BinOp::LtEq
                    | BinOp::GtEq
                    | BinOp::EqEq
                    | BinOp::NotEq => {
                        let bool_ty = ty::bool_ty(self.tcx);
                        // TODO: assert numeric
                        self.icx.eq(lhs_ty, rhs_ty).emit(self.err, expr.span()).ok();
                        bool_ty
                    }
                }
            }

            Unary(op, rhs) => {
                let rhs_ty = self.expr(rhs)?;
                match op {
                    UnaryOp::BitNot | UnaryOp::Neg => {
                        // TODO: assert numeric
                        rhs_ty
                    }
                    UnaryOp::LogNot => {
                        let bool_ty = ty::bool_ty(self.tcx);
                        self.icx.eq(rhs_ty, bool_ty).emit(self.err, rhs.span()).ok();
                        bool_ty
                    }
                    UnaryOp::Deref => {
                        if let TyKind::Pointer(_, inner_ty) = rhs_ty.0 .0 {
                            *inner_ty
                        } else {
                            let ty = self.icx.mk_var();
                            let ptr_ty = ty.ptr(self.tcx);
                            self.icx.eq(ptr_ty, rhs_ty).emit(self.err, rhs.span()).ok();
                            ty
                        }
                    }
                    UnaryOp::Ref | UnaryOp::RefMut | UnaryOp::Box => rhs_ty.ptr(self.tcx),
                }
            }
            Dot(expr, field) => {
                let expr_ty = self.expr(expr)?;
                if let TyKind::Adt(adt) = expr_ty.full_deref_ty().0 .0 {
                    if let Some(ty) = adt.get_field(self.md, field) {
                        ty
                    } else {
                        self.err.err(format!("No such field: {field}"), expr.span());
                        ty::err_ty(self.tcx)
                    }
                } else {
                    let ty = self.icx.mk_var();
                    self.icx
                        .field(expr_ty, field.clone(), ty)
                        .emit(self.err, expr.span())
                        .ok();
                    ty
                }
            }
            Cast(expr, ty) => {
                let _expr_ty = self.expr(expr)?;
                // TODO: check cast compatibility
                *ty
            }
            Range(super::Range::All) => ty::range_ty(self.tcx),
            Range(super::Range::Full(lhs, rhs)) => {
                let usize_ty = ty::primitive_ty(self.tcx, ty::PrimitiveType::USize);
                let lhs_ty = self.expr(lhs)?;
                let rhs_ty = self.expr(rhs)?;
                self.icx
                    .eq(lhs_ty, usize_ty)
                    .emit(self.err, lhs.span())
                    .ok();
                self.icx
                    .eq(rhs_ty, usize_ty)
                    .emit(self.err, rhs.span())
                    .ok();
                ty::range_ty(self.tcx)
            }
            Range(super::Range::Start(lhs)) | Range(super::Range::End(lhs)) => {
                let usize_ty = ty::primitive_ty(self.tcx, ty::PrimitiveType::USize);
                let lhs_ty = self.expr(lhs)?;
                self.icx
                    .eq(lhs_ty, usize_ty)
                    .emit(self.err, lhs.span())
                    .ok();
                ty::range_ty(self.tcx)
            }

            Ternary {
                condition,
                then_expr,
                else_expr,
            } => {
                let condition_ty = self.expr(condition)?;
                let then_expr_ty = self.expr(then_expr)?;
                let else_expr_ty = self.expr(else_expr)?;
                let bool_ty = ty::bool_ty(self.tcx);
                self.icx
                    .eq(condition_ty, bool_ty)
                    .emit(self.err, condition.span())
                    .ok();
                self.icx
                    .eq(then_expr_ty, else_expr_ty)
                    .emit(self.err, condition.span())
                    .ok();
                then_expr_ty
            }
            DotCall {
                expr,
                field,
                arguments,
            } => {
                let expr_ty = self.expr(expr)?;
                let mut argument_tys = arguments
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<InferResult<VecDeque<_>>>()?;
                argument_tys.push_front(expr_ty.ptr(self.tcx));

                if let TyKind::Adt(adt) = expr_ty.full_deref_ty().0 .0 {
                    if let Some(Ty(Int(TyKind::Fun(arg_tys, ret_ty)))) =
                        adt.get_method_ty(self.md, field)
                    {
                        assert_eq!(arg_tys.len(), argument_tys.len());
                        for (l, r) in arg_tys.iter().zip(argument_tys) {
                            self.icx.eq(*l, r).emit(self.err, expr.span()).ok();
                        }
                        *ret_ty
                    } else {
                        self.err
                            .err(format!("No such method: {field}"), expr.span());
                        ty::err_ty(self.tcx)
                    }
                } else {
                    let ret_ty = self.icx.mk_var();
                    let fun_ty = self.tcx.int(TyKind::Fun(argument_tys.into(), ret_ty));
                    self.icx
                        .method(expr_ty, field.clone(), fun_ty)
                        .emit(self.err, expr.span())
                        .ok();
                    ret_ty
                }
            }
            Call { expr, arguments } => {
                let expr_ty = self.expr(expr)?;
                let argument_tys = arguments
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<InferResult<Vec<_>>>()?;
                let ret_ty = self.icx.mk_var();
                let fun_ty = self.tcx.int(TyKind::Fun(argument_tys, ret_ty));
                self.icx
                    .eq(fun_ty, expr_ty)
                    .emit(self.err, expr.span())
                    .ok();
                ret_ty
            }
            Index { expr, index } => {
                let expr_ty = self.expr(expr)?;
                let index_ty = self.expr(index)?;
                self.icx
                    .eq(
                        index_ty,
                        ty::primitive_ty(self.tcx, ty::PrimitiveType::USize),
                    )
                    .emit(self.err, expr.span())
                    .ok();
                let inner_ty = self.icx.mk_var();
                let slice_ty = inner_ty.slice_ty(self.tcx).ptr(self.tcx);
                self.icx
                    .eq(slice_ty, expr_ty)
                    .emit(self.err, expr.span())
                    .ok();
                inner_ty
            }
            Array { members } => {
                let member_tys = members
                    .iter()
                    .map(|expr| self.expr(expr))
                    .collect::<InferResult<Vec<_>>>()?;
                if member_tys.is_empty() {
                    let ty = self.icx.mk_var();
                    self.tcx.int(TyKind::SizedArray(0, ty))
                } else {
                    let first = *member_tys.first().unwrap();
                    for member in member_tys.iter().skip(1) {
                        self.icx.eq(first, *member).emit(self.err, expr.span()).ok();
                    }
                    self.tcx.int(TyKind::SizedArray(members.len(), first))
                }
            }
            Struct {
                ty_name: (ty_name, ty_params),
                members,
            } => {
                if let Some(def_id) = self.md.get_def_id_by_path(ty_name) {
                    let def = self.md.get_def_by_id(def_id);
                    if let Some((ty_param_names, member_tys, _)) = def.get_struct_fields() {
                        if ty_params.is_empty() || ty_param_names.len() == ty_params.len() {
                            let generics: Vec<(String, Ty<'ty>)> = if ty_params.is_empty() {
                                ty_param_names
                                    .iter()
                                    .cloned()
                                    .map(|name| (name, self.icx.mk_var()))
                                    .collect()
                            } else {
                                ty_param_names
                                    .iter()
                                    .cloned()
                                    .zip(ty_params.iter().copied())
                                    .collect()
                            };
                            if member_tys.len() == members.len() {
                                for (expr_name, expr) in members {
                                    if let Some(ty) = member_tys.get(expr_name) {
                                        let ty = replace_generics(self.tcx, *ty, &generics);
                                        let expr_ty = self.expr(expr)?;
                                        self.icx.eq(expr_ty, ty).emit(self.err, expr.span()).ok();
                                    } else {
                                        self.err.err("Unknown field name".to_owned(), expr.span());
                                    }
                                }
                                let ty_params = generics.into_iter().map(|(_, ty)| ty).collect();
                                let ty = TyKind::Adt(AdtType {
                                    def_id,
                                    path: ty_name.clone(),
                                    ty_params,
                                });
                                self.tcx.int(ty)
                            } else {
                                self.err
                                    .err("Missing or extra members".to_owned(), expr.span());
                                ty::err_ty(self.tcx)
                            }
                        } else {
                            self.err.err("Invalid type params".to_owned(), expr.span());
                            ty::err_ty(self.tcx)
                        }
                    } else {
                        self.err.err("Name is not a struct".to_owned(), expr.span());
                        ty::err_ty(self.tcx)
                    }
                } else {
                    self.err.err("Struct not found".to_owned(), expr.span());
                    ty::err_ty(self.tcx)
                }
            }
            Integer(val) => {
                let _pt = match val {
                    IntegerSpecifier::I8(_) => ty::PrimitiveType::I8,
                    IntegerSpecifier::I16(_) => ty::PrimitiveType::I16,
                    IntegerSpecifier::I32(_) => ty::PrimitiveType::I32,
                    IntegerSpecifier::I64(_) => ty::PrimitiveType::I64,
                    IntegerSpecifier::U8(_) => ty::PrimitiveType::U8,
                    IntegerSpecifier::U16(_) => ty::PrimitiveType::U16,
                    IntegerSpecifier::U32(_) => ty::PrimitiveType::U32,
                    IntegerSpecifier::U64(_) => ty::PrimitiveType::U64,
                    IntegerSpecifier::USize(_) => ty::PrimitiveType::USize,
                    IntegerSpecifier::Signed(_) | IntegerSpecifier::Unsigned(_) => {
                        ty::PrimitiveType::Integer
                    }
                };
                // TODO: use definite type where possible
                let ty = self.icx.mk_var();
                self.icx.integral(ty).emit(self.err, expr.span()).ok();
                ty
            }
            Float(val) => {
                let pt = match val {
                    FloatSpecifier::F32(_) => ty::PrimitiveType::F32,
                    FloatSpecifier::F64(_) => ty::PrimitiveType::F64,
                };
                ty::primitive_ty(self.tcx, pt)
            }
            StringExpr(_) => ty::primitive_ty(self.tcx, ty::PrimitiveType::U8)
                .slice_ty(self.tcx)
                .ptr(self.tcx),
            Bool(_) => ty::bool_ty(self.tcx),
        };
        self.tir.set_ty(expr.id(), ty);
        Ok(ty)
    }

    fn solve(&mut self, stmt: &Stmt<'ty>) -> InferResult<()> {
        let replacement = match self.icx.solve() {
            Ok(s) => s,
            Err(InferError::UnableToResolve(id)) => {
                stmt.visit(&mut |_| {}, &mut |e| {
                    let ty = self.tir.get_ty(e.id());
                    if contains_ty_var(id, ty) {
                        self.err
                            .err(format!("Unable to resolve type: {ty}"), e.span());
                    }
                });
                debug!("{:?}", self.icx);
                print_pass_errors_and_exit(self.err);
                panic!();
            }
            Err(e) => {
                panic!("ERROR: {:?}", e);
            }
        };
        // TODO: fix this:
        // self.icx.check(&replacement).unwrap();
        print_pass_errors_and_exit(self.err);
        stmt.visit(&mut |_| {}, &mut |e| {
            if let ExprKind::Ident(_, tys) = e.kind() {
                let mut tys = tys.borrow_mut();
                for ty in tys.iter_mut() {
                    *ty = replace_ty_vars(self.tcx, &replacement, *ty);
                }
            }
        });
        for ty in self.tir.expr_tys.values_mut() {
            *ty = replace_ty_vars(self.tcx, &replacement, *ty);
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Scope<'ty> {
    parent: Option<Box<Scope<'ty>>>,
    variables: HashMap<String, Ty<'ty>>,
}

impl<'ty> Scope<'ty> {
    fn from_params(params: &[(String, Ty<'ty>)]) -> Scope<'ty> {
        Scope {
            parent: None,
            variables: HashMap::from_iter(params.iter().cloned()),
        }
    }

    fn resolve(&self, name: &str) -> Option<Ty<'ty>> {
        match self.variables.get(name) {
            Some(v) => Some(*v),
            None => match &self.parent {
                Some(parent) => parent.resolve(name),
                None => None,
            },
        }
    }

    fn insert(&mut self, name: String, ty: Ty<'ty>) {
        self.variables.insert(name, ty);
    }
}
