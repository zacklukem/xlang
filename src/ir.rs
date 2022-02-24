use crate::ast::{self, Span};
use crate::const_eval::ConstEvaluator;
use crate::intern::Arena;
use crate::symbol::{Name, Symbol, TyCtx};
use crate::ty::Ty;

pub struct Fun<'ty> {
    pub name: Name<'ty>,
    pub variable_defs: Vec<(String, Ty<'ty>)>,
    pub block: Stmt<'ty>,
}

#[derive(Debug)]
pub struct Module<'ty> {
    pub symbols: Vec<Name<'ty>>,
    pub functions: Vec<Fun<'ty>>,
    pub ty_ctx: TyCtx<'ty>,
    pub const_eval: ConstEvaluator,
    pub root: Symbol<'ty>,
}

impl<'ty> Module<'ty> {
    /// Create a new empty module
    pub fn new(ty_ctx: TyCtx<'ty>) -> Module<'ty> {
        Module {
            root: Symbol::Mod {
                symbols: Default::default(),
            },
            ty_ctx,
            functions: Default::default(),
            symbols: Default::default(),
            const_eval: ConstEvaluator {},
        }
    }

    /// Get the module's symbols
    pub fn symbols(&self) -> &Vec<Name> {
        &self.symbols
    }

    /// Get the module ty context
    pub fn ty_ctx(&self) -> TyCtx<'ty> {
        self.ty_ctx
    }

    /// Get the module's const evaluator
    pub fn const_eval(&self) -> &ConstEvaluator {
        &self.const_eval
    }
}

#[derive(Debug)]
pub struct Stmt<'ty> {
    pub kind: StmtKind<'ty>,
    pub span: Span,
}

impl Stmt<'_> {
    pub fn new(kind: StmtKind, span: Span) -> Stmt {
        Stmt { kind, span }
    }
}

#[derive(Debug)]
pub enum StmtKind<'ty> {
    If {
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
        else_block: Option<Box<Stmt<'ty>>>,
    },

    While {
        condition: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    For {
        initializer: Box<Stmt<'ty>>,
        condition: Box<Expr<'ty>>,
        incrementor: Box<Expr<'ty>>,
        block: Box<Stmt<'ty>>,
    },

    Labeled(String, Option<Box<Stmt<'ty>>>),

    Block(Vec<Stmt<'ty>>),
    StmtList(Vec<Stmt<'ty>>),
    Return(Option<Box<Expr<'ty>>>),
    Goto(String),

    Expr(Box<Expr<'ty>>),
}

#[derive(Debug)]
pub struct Expr<'ty> {
    pub kind: ExprKind<'ty>,
    pub span: Span,
    pub ty: Ty<'ty>,
    /// Field to pass to first arg of function
    pub fun_pass: Option<Box<Expr<'ty>>>,
}

impl<'ty> Expr<'ty> {
    pub fn new(kind: ExprKind<'ty>, span: Span, ty: Ty<'ty>) -> Expr<'ty> {
        Expr {
            kind,
            span,
            ty,
            fun_pass: None,
        }
    }

    pub fn new_pass(
        kind: ExprKind<'ty>,
        span: Span,
        ty: Ty<'ty>,
        fun_pass: Box<Expr<'ty>>,
    ) -> Expr<'ty> {
        Expr {
            kind,
            span,
            ty,
            fun_pass: Some(fun_pass),
        }
    }

    pub fn fun_pass(&self) -> &Option<Box<Expr>> {
        &self.fun_pass
    }

    pub fn fun_pass_mut(&mut self) -> &mut Option<Box<Expr<'ty>>> {
        &mut self.fun_pass
    }

    pub fn lhs_expr(self, ctx: TyCtx<'ty>) -> Expr<'ty> {
        let span = self.span.clone();
        let ty = self.ty.mut_ptr(ctx);
        Expr::new(ExprKind::LhsExpr(Box::new(self)), span, ty)
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn ty(&self) -> Ty<'ty> {
        self.ty
    }
}

#[derive(Debug)]
pub enum IntegerSpecifier {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    USize(usize),
    Signed(isize),
    Unsigned(usize),
}

#[derive(Debug)]
pub enum FloatSpecifier {
    F32(f32),
    F64(f64),
}

#[derive(Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Xor,
    Shl,
    Shr,
    And,
    Or,
    AndAnd,
    OrOr,
    Lt,
    Gt,
    LtEq,
    GtEq,
    EqEq,
    NotEq,
}

impl From<&ast::BinOp> for BinOp {
    fn from(op: &ast::BinOp) -> Self {
        match op {
            ast::BinOp::Add => BinOp::Add,
            ast::BinOp::Sub => BinOp::Sub,
            ast::BinOp::Mul => BinOp::Mul,
            ast::BinOp::Div => BinOp::Div,
            ast::BinOp::Mod => BinOp::Mod,
            ast::BinOp::Xor => BinOp::Xor,
            ast::BinOp::Shl => BinOp::Shl,
            ast::BinOp::Shr => BinOp::Shr,
            ast::BinOp::And => BinOp::And,
            ast::BinOp::Or => BinOp::Or,
            ast::BinOp::AndAnd => BinOp::AndAnd,
            ast::BinOp::OrOr => BinOp::OrOr,
            ast::BinOp::Lt => BinOp::Lt,
            ast::BinOp::Gt => BinOp::Gt,
            ast::BinOp::LtEq => BinOp::LtEq,
            ast::BinOp::GtEq => BinOp::GtEq,
            ast::BinOp::EqEq => BinOp::EqEq,
            ast::BinOp::NotEq => BinOp::NotEq,
        }
    }
}

#[derive(Debug)]
pub enum AssignOp {
    Eq,
    AddEq,
    SubEq,
    MulEq,
    DivEq,
    ModEq,
    XorEq,
    AndEq,
    OrEq,
}

impl From<&ast::AssignOp> for AssignOp {
    fn from(v: &ast::AssignOp) -> Self {
        match v {
            ast::AssignOp::Eq => AssignOp::Eq,
            ast::AssignOp::AddEq => AssignOp::AddEq,
            ast::AssignOp::SubEq => AssignOp::SubEq,
            ast::AssignOp::MulEq => AssignOp::MulEq,
            ast::AssignOp::DivEq => AssignOp::DivEq,
            ast::AssignOp::ModEq => AssignOp::ModEq,
            ast::AssignOp::XorEq => AssignOp::XorEq,
            ast::AssignOp::AndEq => AssignOp::AndEq,
            ast::AssignOp::OrEq => AssignOp::OrEq,
        }
    }
}

#[derive(Debug)]
pub enum UnaryOp {
    Neg,
    LogNot,
    BitNot,
    Deref,
    Ref,
    RefMut,
    Box,
}

impl From<&ast::UnaryOp> for UnaryOp {
    fn from(op: &ast::UnaryOp) -> Self {
        match op {
            ast::UnaryOp::Neg => UnaryOp::Neg,
            ast::UnaryOp::LogNot => UnaryOp::LogNot,
            ast::UnaryOp::BitNot => UnaryOp::BitNot,
            ast::UnaryOp::Deref => UnaryOp::Deref,
            ast::UnaryOp::Ref => UnaryOp::Ref,
            ast::UnaryOp::RefMut => UnaryOp::RefMut,
            ast::UnaryOp::Box => UnaryOp::Box,
        }
    }
}

#[derive(Debug)]
pub enum ExprKind<'ty> {
    Ident(Name<'ty>),
    Integer(IntegerSpecifier),
    Float(FloatSpecifier),
    String(String),
    Bool(bool),

    Null,

    LhsExpr(Box<Expr<'ty>>),

    Tuple(Vec<Expr<'ty>>),

    Assign(Box<Expr<'ty>>, AssignOp, Box<Expr<'ty>>),
    Binary(Box<Expr<'ty>>, BinOp, Box<Expr<'ty>>),
    Unary(UnaryOp, Box<Expr<'ty>>),
    Dot(Box<Expr<'ty>>, String),
    Cast(Box<Expr<'ty>>, Ty<'ty>),

    Range(Box<Expr<'ty>>, Box<Expr<'ty>>),
    RangeFrom(Box<Expr<'ty>>),

    Ternary {
        condition: Box<Expr<'ty>>,
        then_expr: Box<Expr<'ty>>,
        else_expr: Box<Expr<'ty>>,
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

    // [a, b, c, d]
    Array {
        members: Vec<Expr<'ty>>,
    },

    // MyStruct { name: value, name: value }
    Struct {
        type_name: Name<'ty>,
        members: Vec<(String, Box<Expr<'ty>>)>,
    },

    Err,
}
