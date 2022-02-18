use std::rc::Rc;

pub struct Source {
    pub source_string: String,
}

#[derive(Clone)]
pub struct Span {
    pub source: Rc<Source>,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn str(&self) -> &str {
        &self.source.source_string[self.start..self.end]
    }
    pub fn var_str(&self) -> String {
        format!("_{}", self.start)
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(fmt, "('{}', {}..{})", self.str(), self.start, self.end)
    }
}

pub struct Spanned<T> {
    pub span: Span,
    pub value: T,
}

impl<T> Spanned<T> {
    pub fn value(&self) -> &T {
        &self.value
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Spanned<T> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(fmt, "{:#?}{:#?}", self.span, self.value)
    }
}

pub type SpanBox<T> = Box<Spanned<T>>;
pub type SpanVec<T> = Vec<Spanned<T>>;

pub struct Ident {
    pub span: Span,
}

impl Ident {
    pub fn str(&self) -> &str {
        self.span.str()
    }
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(fmt, "Ident{:?}", self.span)
    }
}

#[derive(Debug)]
pub enum Name {
    Ident(Ident),
    Namespace(Ident, Span, SpanBox<Name>),
}

#[derive(Debug)]
pub enum Pattern {
    Tuple(Span, SpanVec<Pattern>, Span),
    Ident(Ident),
}

#[derive(Debug)]
pub enum SelfType {
    Star,
    StarMut,
}

#[derive(Debug)]
pub struct Module {
    pub top_stmts: SpanVec<TopStmt>,
}

#[derive(Debug)]
pub struct FunFinally {
    pub block: SpanBox<Stmt>,
}

#[derive(Debug)]
pub struct FunBlock {
    pub stmts: SpanVec<Stmt>,
    pub finally: Option<FunFinally>,
}

pub type FunParams = (Option<Spanned<SelfType>>, SpanVec<(Ident, SpanBox<Type>)>);

#[derive(Debug)]
pub enum TopStmt {
    Fun {
        pub_tok: Option<Span>,
        fun_tok: Span,
        name: SpanBox<Name>,
        params: FunParams,
        return_type: Option<SpanBox<Type>>,
        body: SpanBox<FunBlock>,
    },
    Struct {
        pub_tok: Option<Span>,
        struct_tok: Span,
        name: SpanBox<Name>,
        members: SpanVec<(Ident, SpanBox<Type>)>,
    },
}

#[derive(Debug)]
pub enum Stmt {
    If {
        if_tok: Span,
        condition: SpanBox<Expr>,
        block: SpanBox<Stmt>,
        else_block: Option<SpanBox<Stmt>>,
    },

    While {
        label: Option<Ident>,
        while_tok: Span,
        condition: SpanBox<Expr>,
        block: SpanBox<Stmt>,
    },

    Loop {
        label: Option<Ident>,
        loop_tok: Span,
        block: SpanBox<Stmt>,
    },

    ForRange {
        label: Option<Ident>,
        for_tok: Span,
        initializer: SpanBox<Pattern>,
        in_tok: Span,
        range: SpanBox<Expr>,
        block: SpanBox<Stmt>,
    },

    Let {
        let_tok: Span,
        pattern: SpanBox<Pattern>,
        type_name: Option<SpanBox<Type>>,
        eq_tok: Span,
        expr: SpanBox<Expr>,
    },

    Block(Span, SpanVec<Stmt>, Span),
    Return(Span, Option<SpanBox<Expr>>),
    Continue(Span, Option<Ident>),
    Break(Span, Option<Ident>),

    Expr(SpanBox<Expr>),
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
pub enum Range {
    All(Span),
    Start(SpanBox<Expr>, Span),
    End(Span, SpanBox<Expr>),
    Full(SpanBox<Expr>, Span, SpanBox<Expr>),
}

#[derive(Debug)]
pub enum IntegerSpecifier {
    I8,
    I16,
    I32,
    I64,

    U8,
    U16,
    U32,
    U64,
    USize,
    None,
}

#[derive(Debug)]
pub enum FloatSpecifier {
    F32,
    F64,
    None,
}

#[derive(Debug)]
pub enum Expr {
    Ident(Name),
    Integer(Span, IntegerSpecifier),
    Float(Span, FloatSpecifier),
    String(Span),
    Bool(Span, bool),

    Tuple(Span, SpanVec<Expr>, Span),

    Assign(SpanBox<Expr>, Spanned<AssignOp>, SpanBox<Expr>),
    Binary(SpanBox<Expr>, Spanned<BinOp>, SpanBox<Expr>),
    Unary(Spanned<UnaryOp>, SpanBox<Expr>),
    Dot(SpanBox<Expr>, Span, Ident),
    Cast(SpanBox<Expr>, Span, SpanBox<Type>),

    Range(Range),

    Ternary {
        if_tok: Span,
        condition: SpanBox<Expr>,
        then_tok: Span,
        then_expr: SpanBox<Expr>,
        else_tok: Span,
        else_expr: SpanBox<Expr>,
    },

    // expr(index, ...)
    Call {
        expr: SpanBox<Expr>,
        left_paren: Span,
        arguments: SpanVec<Expr>,
        right_paren: Span,
    },

    // expr[index]
    Index {
        expr: SpanBox<Expr>,
        left_bracket: Span,
        index: SpanBox<Expr>,
        right_bracket: Span,
    },

    // [a, b, c, d]
    Array {
        left_bracket: Span,
        members: SpanVec<Expr>,
        right_bracket: Span,
    },

    // MyStruct { name: value, name: value }
    Struct {
        type_name: SpanBox<Name>,
        left_brace: Span,
        members: SpanVec<(Ident, SpanBox<Expr>)>,
        right_brace: Span,
    },
}

// Types

#[derive(Debug)]
pub enum PrimitiveType {
    I8,
    I16,
    I32,
    I64,

    U8,
    U16,
    U32,
    U64,
    USize,

    F32,
    F64,

    Bool,
    Void,
}

#[derive(Debug)]
pub enum PointerType {
    StarMut,
    Star,
}

#[derive(Debug)]
pub enum Type {
    // i8, u8, bool, ...
    Primitive(Spanned<PrimitiveType>),

    // MyStruct, YourStruct, ...
    Named(SpanBox<Name>),

    // *mut *[]i8
    Pointer(Spanned<PointerType>, SpanBox<Type>),

    // (i8, i16)
    Tuple(Span, SpanVec<Type>, Span),

    // (i8) -> void
    Fun(SpanVec<Type>, Option<SpanBox<Type>>),

    // [8]i8
    SizedArray {
        left_bracket: Span,
        size: SpanBox<Expr>,
        right_bracket: Span,
        inner_type: SpanBox<Type>,
    },

    // []i8
    UnsizedArray {
        left_bracket: Span,
        right_bracket: Span,
        inner_type: SpanBox<Type>,
    },
}
