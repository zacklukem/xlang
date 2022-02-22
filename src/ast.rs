use std::rc::Rc;

pub struct Source {
    pub source_string: String,
    /// Indices of first char in each line
    line_starts: Vec<usize>,
}

impl Source {
    pub fn new(source_string: String) -> Source {
        let mut line_starts = Vec::new();

        {
            line_starts.push(0);
            for (idx, ch) in source_string.chars().enumerate() {
                if ch == '\n' {
                    line_starts.push(idx + 1);
                }
            }
        }

        Source {
            source_string,
            line_starts,
        }
    }

    pub fn print_msg(&self, (start, end): (usize, usize), msg: &str) {
        let (line_num, col) = self.line_col(start);
        let line_start = self.line_starts[line_num - 1];
        let line_end = self.line_starts[line_num];
        let line = &self.source_string[line_start..line_end];
        let line = line.trim_end();
        println!("     --> Error: {}:{}", line_num + 1, col);
        print!("      | \n{:>5} | {}\n      | ", line_num + 1, line);
        println!(
            "{:left$}{:^>width$} {}\n      |",
            "",
            "",
            msg,
            left = col - 1,
            width = end - start
        );
    }

    pub fn line_col(&self, pos: usize) -> (usize, usize) {
        let (line, idx) = self
            .line_starts
            .iter()
            .enumerate()
            .find(|(_, idx)| **idx > pos)
            .unwrap();
        let idx = self.line_starts[line - 1];
        (line, (pos - idx) + 1)
    }
}

#[derive(Clone)]
pub struct Span {
    pub source: Rc<Source>,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn dummy() -> Span {
        Span {
            source: Rc::new(Source::new(String::new())),
            start: 0,
            end: 0,
        }
    }

    pub fn print_msg(&self, msg: &str) {
        self.source.print_msg(self.as_tuple(), msg)
    }

    pub fn as_tuple(&self) -> (usize, usize) {
        (self.start, self.end)
    }

    pub fn str(&self) -> &str {
        &self.source.source_string[self.start..self.end]
    }

    pub fn var_str(&self) -> String {
        format!("_{}", self.start)
    }

    pub fn line_col(&self) -> (usize, usize) {
        self.source.line_col(self.start)
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
    Ident(Ident, SpanVec<Type>),
    Namespace(Ident, SpanVec<Type>, Span, SpanBox<Name>),
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
        type_params: Vec<Span>,
        name: SpanBox<Name>,
        params: FunParams,
        return_type: Option<SpanBox<Type>>,
        body: SpanBox<FunBlock>,
    },
    Struct {
        pub_tok: Option<Span>,
        struct_tok: Span,
        type_params: Vec<Span>,
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
        mut_tok: Option<Span>,
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
    Box,
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

    Null(Span),

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
