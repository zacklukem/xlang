pub mod ast_lower;
pub mod tir_infer;
pub mod visit;

use crate::ast::{self, Span};
use crate::error_context::ErrorContext;
use crate::ir::{self, AssignOp, BinOp, InlineCParamType, Path, UnaryOp};
use crate::mod_gen::ModGenError;
use crate::ty::Ty;
use std::cell::Cell;
use std::collections::HashMap;

pub fn lower_and_type_ast<'ty>(
    md: &ir::Module<'ty>,
    tir: &mut TirCtx<'ty>,
    err: &mut ErrorContext,
    return_type: Ty<'ty>,
    params: Vec<(String, Ty<'ty>)>,
    usages: &HashMap<String, ir::Path>,
    current_generics: Vec<String>,
    fun_block: &ast::Spanned<ast::FunBlock>,
) -> Result<Stmt<'ty>, ModGenError> {
    let stmt = ast_lower::lower_ast(md, tir, err, usages, &current_generics, fun_block)?;
    tir_infer::tir_infer(md, tir, err, return_type, &params, &stmt)?;
    stmt.visit(
        |_| {},
        |expr| {
            if !tir.expr_tys.contains_key(&expr.id()) {
                println!("UNTYPED: {:?}", expr);
                expr.span().print_msg("UNTYPED!!", "ERROR!")
            } else {
                expr.span().print_msg(
                    &format!("{}", tir.get_ty(expr.id())),
                    &format!("{:?}", expr),
                );
            }
        },
    );
    Ok(stmt)
}

#[derive(Default)]
pub struct TirCtx<'ty> {
    next_stmt: Cell<u32>,
    next_expr: Cell<u32>,
    expr_tys: HashMap<ExprId, Ty<'ty>>,
    stmt_tys: HashMap<StmtId, Ty<'ty>>,
}

impl<'ty> TirCtx<'ty> {
    fn mk_expr_id(&self) -> ExprId {
        let id = self.next_expr.get();
        self.next_expr.set(id + 1);
        ExprId(id)
    }

    fn mk_stmt_id(&self) -> StmtId {
        let id = self.next_stmt.get();
        self.next_stmt.set(id + 1);
        StmtId(id)
    }

    pub fn mk_expr(&self, kind: ExprKind<'ty>, span: Span) -> Expr<'ty> {
        let id = self.mk_expr_id();
        Expr { id, span, kind }
    }

    pub fn mk_stmt(&self, kind: StmtKind<'ty>, span: Span) -> Stmt<'ty> {
        let id = self.mk_stmt_id();
        Stmt { id, span, kind }
    }

    pub fn set_ty(&mut self, id: ExprId, ty: Ty<'ty>) {
        self.expr_tys.insert(id, ty);
    }

    #[track_caller]
    pub fn get_ty(&self, id: ExprId) -> Ty<'ty> {
        *self.expr_tys.get(&id).expect("Get ty after types not set")
    }

    pub fn set_stmt_ty(&mut self, id: StmtId, ty: Ty<'ty>) {
        self.stmt_tys.insert(id, ty);
    }

    pub fn get_stmt_ty(&self, id: StmtId) -> Ty<'ty> {
        *self.stmt_tys.get(&id).expect("Get ty on non let stmt")
    }
}

#[derive(Debug, Clone)]
pub struct Pattern(pub Span, pub PatternKind);

#[derive(Debug, Clone)]
pub enum PatternKind {
    Variant(Path, Box<Pattern>),
    Tuple(Vec<Pattern>),
    Ident(String),
}

#[derive(Debug, Clone)]
pub struct Arm<'ty> {
    pub pattern: Box<Pattern>,
    pub stmts: Vec<Stmt<'ty>>,
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub struct StmtId(u32);

#[derive(Debug, Clone)]
pub struct Stmt<'ty> {
    kind: StmtKind<'ty>,
    span: Span,
    id: StmtId,
}

impl<'ty> Stmt<'ty> {
    pub fn kind(&self) -> &StmtKind<'ty> {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn id(&self) -> StmtId {
        self.id
    }
}

#[derive(Debug, Clone)]
pub enum StmtKind<'ty> {
    If {
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
        else_block: Option<Box<Stmt<'ty>>>,
    },

    While {
        label: Option<String>,
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    Loop {
        label: Option<String>,
        block: Box<Stmt<'ty>>,
    },

    Case {
        expr: Box<Expr<'ty>>,
        arms: Vec<Arm<'ty>>,
    },

    ForRange {
        label: Option<String>,
        initializer: Box<Pattern>,
        range: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    Let {
        mutable: bool,
        pattern: Box<Pattern>,
        type_name: Option<Ty<'ty>>,
        expr: Box<Expr<'ty>>,
    },

    InlineC {
        inputs: Vec<(InlineCParamType, String, String)>,
        outputs: Vec<(String, InlineCParamType, String)>,
        code: String,
    },

    Block(Vec<Stmt<'ty>>),
    Return(Option<Box<Expr<'ty>>>),
    Continue(Option<String>),
    Break(Option<String>),

    Expr(Box<Expr<'ty>>),
}

#[derive(Debug, Clone)]
pub enum Range<'ty> {
    All,
    Start(Box<Expr<'ty>>),
    End(Box<Expr<'ty>>),
    Full(Box<Expr<'ty>>, Box<Expr<'ty>>),
}

#[derive(Debug, Clone)]
pub enum IntegerSpecifier {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    U8(i8),
    U16(i16),
    U32(i32),
    U64(i64),
    USize(usize),
    Signed(isize),
    Unsigned(usize),
}

#[derive(Debug, Clone)]
pub enum FloatSpecifier {
    F32(f32),
    F64(f64),
    None(String),
}

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub struct ExprId(u32);

#[derive(Debug, Clone)]
pub struct Expr<'ty> {
    kind: ExprKind<'ty>,
    id: ExprId,
    span: Span,
}

impl<'ty> Expr<'ty> {
    pub fn kind(&self) -> &ExprKind<'ty> {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn id(&self) -> ExprId {
        self.id
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind<'ty> {
    Ident(Path, Vec<Ty<'ty>>),
    Integer(IntegerSpecifier),
    Float(FloatSpecifier),
    String(String),
    Bool(bool),

    Null,

    Tuple(Vec<Expr<'ty>>),

    Assign(Box<Expr<'ty>>, AssignOp, Box<Expr<'ty>>),
    Binary(Box<Expr<'ty>>, BinOp, Box<Expr<'ty>>),
    Unary(UnaryOp, Box<Expr<'ty>>),
    Dot(Box<Expr<'ty>>, String),
    Cast(Box<Expr<'ty>>, Ty<'ty>),

    Range(Range<'ty>),

    Ternary {
        condition: Box<Expr<'ty>>,
        then_expr: Box<Expr<'ty>>,
        else_expr: Box<Expr<'ty>>,
    },

    // expr.field(index, ...)
    DotCall {
        expr: Box<Expr<'ty>>,
        field: String,
        arguments: Vec<Expr<'ty>>,
    },

    // expr(index, ...)
    Call {
        expr: Box<Expr<'ty>>,
        arguments: Vec<Expr<'ty>>,
    },

    // expr[index]
    Index {
        expr: Box<Expr<'ty>>,
        index: Box<Expr<'ty>>,
    },

    Array {
        members: Vec<Expr<'ty>>,
    },

    Struct {
        ty_name: (Path, Vec<Ty<'ty>>),
        members: Vec<(String, Box<Expr<'ty>>)>,
    },
}
