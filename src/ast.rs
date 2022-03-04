//! Abstract syntax tree representation for xlang
//!
//! Contains a faithful representation of the source code with `Span`s to mark
//! the source code locations to ast values

use either::Either;
use std::cell::RefCell;
use std::rc::Rc;

pub struct Source {
    pub source_string: String,
    pub file_name: String,
    /// Indices of first char in each line
    line_starts: Vec<usize>,
}

impl Source {
    pub fn new(file_name: String, source_string: String) -> Source {
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
            file_name,
            line_starts,
        }
    }

    pub fn print_msg(&self, (start, end): (usize, usize), msg: &str, kind: &str) {
        let (line_num, col) = self.line_col(start);
        let line_start = self.line_starts[line_num - 1];
        let line_end = self
            .line_starts
            .get(line_num)
            .copied()
            .unwrap_or(self.source_string.len());
        let line = &self.source_string[line_start..line_end];
        let line = line.trim_end();
        println!(
            "     --> {}: {}:{}:{}",
            kind, &self.file_name, line_num, col
        );
        print!("      | \n{:>5} | {}\n      | ", line_num, line);
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
        let (line, _) = self
            .line_starts
            .iter()
            .enumerate()
            .find(|(_, idx)| **idx > pos)
            .unwrap_or((1, &0));
        let idx = self.line_starts[line - 1];
        (line, (pos - idx) + 1)
    }
}

#[derive(Clone)]
pub struct Span {
    pub source: Rc<Source>,
    pub macro_str: Option<String>,
    pub start: usize,
    pub end: usize,
}

impl std::ops::Add for &Span {
    type Output = Span;

    fn add(self, rhs: &Span) -> Self::Output {
        assert!(std::ptr::eq(self.source.as_ref(), rhs.source.as_ref()));
        if self.macro_str.is_some() {
            Span {
                source: self.source.clone(),
                start: 0,
                end: 0,
                macro_str: Some("CAT_SPAN".to_owned()),
            }
        } else {
            let start = self.start.min(rhs.start);
            let end = self.end.max(rhs.end);
            Span {
                source: self.source.clone(),
                start,
                end,
                macro_str: None,
            }
        }
    }
}

impl Span {
    pub fn dummy() -> Span {
        Span {
            source: Rc::new(Source::new(String::new(), String::new())),
            start: 0,
            end: 0,
            macro_str: None,
        }
    }

    pub fn from_macro_str(s: &str, span: &Span) -> Span {
        Span {
            source: span.source.clone(),
            start: span.start,
            end: span.end,
            macro_str: Some(s.to_owned()),
        }
    }

    pub fn print_msg(&self, msg: &str, kind: &str) {
        self.source.print_msg(self.as_tuple(), msg, kind)
    }

    pub fn as_tuple(&self) -> (usize, usize) {
        (self.start, self.end)
    }

    pub fn str(&self) -> &str {
        if let Some(string) = &self.macro_str {
            string
        } else {
            &self.source.source_string[self.start..self.end]
        }
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

#[derive(Clone)]
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
pub type SpanSlice<T> = [Spanned<T>];

#[derive(Clone)]
pub struct Ident {
    pub span: Span,
}

impl Ident {
    pub fn str(&self) -> &str {
        self.span.str()
    }
    pub fn from_macro_str(s: &str, span: &Span) -> Ident {
        Ident {
            span: Span::from_macro_str(s, span),
        }
    }
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(fmt, "Ident{:?}", self.span)
    }
}

#[derive(Debug, Clone)]
pub enum Name {
    Ident(Ident, SpanVec<Type>),
    Namespace(Ident, SpanVec<Type>, Span, SpanBox<Name>),
}

impl Name {
    pub fn is_ident(&self) -> bool {
        matches!(self, Name::Ident(..))
    }

    pub fn ident_str(&self) -> Option<String> {
        match self {
            Name::Ident(id, _) => Some(id.str().into()),
            _ => None,
        }
    }

    pub fn pop_end(&self) -> Option<Name> {
        use Name::*;
        match self {
            Ident(..) => None,
            Namespace(name, types, _, next) if next.value().is_ident() => {
                Some(Ident(name.clone(), types.clone()))
            }
            Namespace(name, types, colon, next) => Some(Namespace(
                name.clone(),
                types.clone(),
                colon.clone(),
                Box::new(Spanned {
                    value: next.value().pop_end().unwrap(),
                    span: next.span.clone(),
                }),
            )),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Pattern {
    Variant(SpanBox<Name>, Span, SpanVec<Pattern>, Span),
    Tuple(Span, SpanVec<Pattern>, Span),
    Ident(SpanBox<Name>),
}

#[derive(Debug, Clone)]
pub enum SelfType {
    Star,
    StarMut,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub top_stmts: SpanVec<TopStmt>,
}

#[derive(Debug, Clone)]
pub struct FunFinally {
    pub block: SpanBox<Stmt>,
}

#[derive(Debug, Clone)]
pub struct FunBlock {
    pub stmts: SpanVec<Stmt>,
    pub finally: Option<FunFinally>,
}

pub type FunParams = (Option<Spanned<SelfType>>, SpanVec<(Ident, SpanBox<Type>)>);

#[derive(Debug, Clone)]
pub enum TopStmt {
    Use(Span, SpanBox<Name>),
    FunDecl {
        extern_tok: Option<Span>,
        pub_tok: Option<Span>,
        fun_tok: Span,
        type_params: Vec<Span>,
        name: SpanBox<Name>,
        params: FunParams,
        return_type: Option<SpanBox<Type>>,
    },
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
    Enum {
        pub_tok: Option<Span>,
        enum_tok: Span,
        type_params: Vec<Span>,
        name: SpanBox<Name>,
        variants: SpanVec<(Ident, SpanVec<Type>)>,
    },
}

#[derive(Debug, Clone)]
pub struct Arm {
    pub bar_tok: Span,
    pub pattern: SpanBox<Pattern>,
    pub arrow: Span,
    pub stmts: SpanVec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum InlineCParamType {
    Var,
    Type,
}

#[derive(Debug, Clone)]
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

    Case {
        case_tok: Span,
        expr: SpanBox<Expr>,
        open_brace: Span,
        arms: SpanVec<Arm>,
        close_brace: Span,
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

    InlineC {
        at_c: Span,
        inputs: Vec<(InlineCParamType, Span, Span)>,
        outputs: Vec<(Span, InlineCParamType, Span)>,
        code: Span,
    },

    Block(Span, SpanVec<Stmt>, Span),
    Return(Span, Option<SpanBox<Expr>>),
    Continue(Span, Option<Ident>),
    Break(Span, Option<Ident>),

    Expr(SpanBox<Expr>),
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Neg,
    LogNot,
    BitNot,
    Deref,
    Ref,
    RefMut,
    Box,
}

#[derive(Debug, Clone)]
pub enum Range {
    All(Span),
    Start(SpanBox<Expr>, Span),
    End(Span, SpanBox<Expr>),
    Full(SpanBox<Expr>, Span, SpanBox<Expr>),
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum FloatSpecifier {
    F32,
    F64,
    None,
}

#[derive(Debug, Clone)]
pub struct MacroCall {
    pub name: Span,
    pub left_paren: Span,
    pub arguments: SpanVec<Expr>,
    pub right_paren: Span,
}

#[derive(Debug, Clone)]
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

    MacroCall(RefCell<Either<MacroCall, SpanBox<Expr>>>),

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

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub enum PointerType {
    StarMut,
    Star,
}

#[derive(Debug, Clone)]
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
