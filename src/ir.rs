use crate::ast::Span;
use crate::const_eval::ConstEvaluator;
use crate::symbol::{Name, Symbol, TyCtx, Type};

#[derive(Debug)]
pub struct Fun {
    pub name: Name,
    pub variable_defs: Vec<(String, Type)>,
    pub block: Stmt,
}

#[derive(Debug)]
pub struct Module {
    pub symbols: Vec<Name>,
    pub functions: Vec<Fun>,
    pub ty_ctx: TyCtx,
    pub const_eval: ConstEvaluator,
}

impl Module {
    pub fn new() -> Module {
        let ty_ctx = TyCtx {
            root: Symbol::Mod {
                symbols: Default::default(),
            },
        };
        Module {
            ty_ctx,
            functions: Default::default(),
            symbols: Default::default(),
            const_eval: ConstEvaluator {},
        }
    }
    pub fn symbols(&self) -> &Vec<Name> {
        &self.symbols
    }
    pub fn ty_ctx(&self) -> &TyCtx {
        &self.ty_ctx
    }
    pub fn ty_ctx_mut(&mut self) -> &mut TyCtx {
        &mut self.ty_ctx
    }
    pub fn const_eval(&self) -> &ConstEvaluator {
        &self.const_eval
    }
}

#[derive(Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl Stmt {
    pub fn new(kind: StmtKind, span: Span) -> Stmt {
        Stmt { kind, span }
    }
}

#[derive(Debug)]
pub enum StmtKind {
    If {
        condition: Box<Expr>,
        block: Box<Stmt>,
        else_block: Option<Box<Stmt>>,
    },

    While {
        condition: Box<Expr>,
        block: Box<Stmt>,
    },

    For {
        initializer: Box<Stmt>,
        condition: Box<Expr>,
        incrementor: Box<Expr>,
        block: Box<Stmt>,
    },

    // Let {
    //     name: String,
    //     type_name: Box<Type>,
    //     expr: Box<Expr>,
    // },
    Labeled(String, Option<Box<Stmt>>),

    Block(Vec<Stmt>),
    StmtList(Vec<Stmt>),
    Return(Option<Box<Expr>>),
    Goto(String),

    Expr(Box<Expr>),
}

#[derive(Debug)]
pub struct Expr {
    kind: ExprKind,
    span: Span,
    ty: Type,
}

impl Expr {
    pub fn new(kind: ExprKind, span: Span, ty: Type) -> Expr {
        Expr { kind, span, ty }
    }

    pub fn lhs_expr(self) -> Expr {
        let span = self.span.clone();
        let ty = self.ty.mut_ptr();
        Expr::new(ExprKind::LhsExpr(Box::new(self)), span, ty)
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }
    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn ty(&self) -> &Type {
        &self.ty
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

#[derive(Debug)]
pub enum UnaryOp {
    Neg,
    LogNot,
    BitNot,
    Deref,
    Ref,
    RefMut,
}

#[derive(Debug)]
pub enum ExprKind {
    Ident(Name),
    Integer(IntegerSpecifier),
    Float(FloatSpecifier),
    String(String),
    Bool(bool),

    LhsExpr(Box<Expr>),

    Tuple(Vec<Expr>),

    Assign(Box<Expr>, AssignOp, Box<Expr>),
    Binary(Box<Expr>, BinOp, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Dot(Box<Expr>, String),
    Cast(Box<Expr>, Box<Type>),

    Range(Box<Expr>, Box<Expr>),

    Ternary {
        condition: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },

    // expr(index, ...)
    Call {
        expr: Box<Expr>,
        arguments: Vec<Expr>,
    },

    // expr[index]
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },

    // [a, b, c, d]
    Array {
        members: Vec<Expr>,
    },

    // MyStruct { name: value, name: value }
    Struct {
        type_name: Box<Name>,
        left_brace: Span,
        members: Vec<(String, Box<Expr>)>,
        right_brace: Span,
    },
}
