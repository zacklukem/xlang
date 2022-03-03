use std::iter::{Iterator, Peekable};
use std::str::CharIndices;

#[derive(Debug)]
pub enum LexerError {
    /// Unexpected character {0}
    UnexpectedCharacter(char),
    /// Invalid punctuation characters (operators/delimiters)
    InvalidPunctuation,
    /// Expected quote
    ExpectedQuote,
    /// Bad string escape
    BadStringEscape,
}

use LexerError::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token {
    /// regular idents (e.g. _hell0_w0r1d)
    Ident,
    /// Macro idents (e.g. @check)
    MacroIdent,
    /// Inline C macro ident (@c)
    InlineCMacroIdent,
    /// Inline C replacement ident ($arg_name)
    InlineCReplacementIdent,
    /// Floating point number literal
    Float,
    /// Integral number literal
    Integer,
    /// String literal
    String,

    // Punctuation
    Semi,
    Comma,
    Arrow,
    ColonColon,
    Colon,
    OpenParen,
    CloseParen,
    OpenBrack,
    CloseBrack,
    OpenBrace,
    CloseBrace,
    Lt,
    Gt,
    LtEq,
    GtEq,
    EqEq,
    BangEq,
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    CaretEq,
    AndEq,
    BarEq,
    BarBar,
    AndAnd,
    Bar,
    And,
    Caret,
    LtLt,
    GtGt,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    DotDot,
    AtDotDot,
    DotDotAt,
    AtAt,
    Bang,
    Tilde,
    Dot,

    // Keywords
    SelfKey,
    MutKey,
    FinallyKey,
    UseKey,
    ExternKey,
    PubKey,
    FunKey,
    StructKey,
    EnumKey,
    IfKey,
    ElseKey,
    VarKey,
    TypeKey,
    CaseKey,
    WhileKey,
    LoopKey,
    ForKey,
    LetKey,
    RetKey,
    ContinueKey,
    BreakKey,
    ThenKey,
    AsKey,
    OfKey,
    InKey,
    BoxKey,
    NullKey,
    TrueKey,
    FalseKey,
    I8Key,
    I16Key,
    I32Key,
    I64Key,
    U8Key,
    U16Key,
    U32Key,
    U64Key,
    UsizeKey,
    F32Key,
    F64Key,
    BoolKey,
    VoidKey,
}

fn match_keyword(s: &str) -> Option<Token> {
    use Token::*;
    match s {
        "self" => Some(SelfKey),
        "mut" => Some(MutKey),
        "finally" => Some(FinallyKey),
        "use" => Some(UseKey),
        "extern" => Some(ExternKey),
        "pub" => Some(PubKey),
        "fun" => Some(FunKey),
        "struct" => Some(StructKey),
        "enum" => Some(EnumKey),
        "if" => Some(IfKey),
        "else" => Some(ElseKey),
        "var" => Some(VarKey),
        "type" => Some(TypeKey),
        "case" => Some(CaseKey),
        "while" => Some(WhileKey),
        "loop" => Some(LoopKey),
        "for" => Some(ForKey),
        "let" => Some(LetKey),
        "ret" => Some(RetKey),
        "continue" => Some(ContinueKey),
        "break" => Some(BreakKey),
        "then" => Some(ThenKey),
        "as" => Some(AsKey),
        "of" => Some(OfKey),
        "in" => Some(InKey),
        "box" => Some(BoxKey),
        "null" => Some(NullKey),
        "true" => Some(TrueKey),
        "false" => Some(FalseKey),
        "i8" => Some(I8Key),
        "i16" => Some(I16Key),
        "i32" => Some(I32Key),
        "i64" => Some(I64Key),
        "u8" => Some(U8Key),
        "u16" => Some(U16Key),
        "u32" => Some(U32Key),
        "u64" => Some(U64Key),
        "usize" => Some(UsizeKey),
        "f32" => Some(F32Key),
        "f64" => Some(F64Key),
        "bool" => Some(BoolKey),
        "void" => Some(VoidKey),
        _ => None,
    }
}

fn is_ident_later(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn is_ident_first(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

#[derive(Debug)]
struct Scanner<'a> {
    text: &'a str,
    source: Peekable<CharIndices<'a>>,
    start: usize,
    end: usize,
}

impl Scanner<'_> {
    fn new(text: &str) -> Scanner {
        let source = text.char_indices().peekable();
        Scanner {
            text,
            source,
            start: 0,
            end: 0,
        }
    }

    fn skip(&mut self) {
        self.start = self.end;
    }

    fn next(&mut self) -> Option<char> {
        if let Some((idx, ch)) = self.source.next() {
            assert_eq!(idx, self.end);
            self.end = idx + ch.len_utf8();
            Some(ch)
        } else {
            None
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.source.peek().map(|(_, ch)| *ch)
    }

    fn peek2(&mut self) -> Option<char> {
        self.source.clone().nth(1).map(|(_, ch)| ch)
    }

    fn eat(&mut self, ch: char) -> bool {
        if self.peek() == Some(ch) {
            self.next();
            true
        } else {
            false
        }
    }

    fn consume<F>(&mut self, mut fun: F) -> usize
    where
        F: FnMut(char) -> bool + Clone,
    {
        let end = self.end;
        while let Some(c) = self.peek() {
            if !(fun(c)) {
                break;
            }
            self.next();
        }
        self.end - end
    }

    fn current(&self) -> &str {
        &self.text[self.start..self.end]
    }
}

#[derive(Debug)]
pub struct Lexer<'a> {
    sc: Scanner<'a>,
}

impl Lexer<'_> {
    pub fn new(text: &str) -> Lexer {
        Lexer {
            sc: Scanner::new(text),
        }
    }

    fn next_tok(&mut self) -> Option<Result<Token, LexerError>> {
        let c = self.sc.next()?;
        let result = match c {
            // Line comment
            '-' if self.sc.eat('-') => {
                self.sc.consume(|c| c != '\n');
                self.sc.skip();
                self.next_tok()?
            }

            // Strings
            '"' => {
                self.sc.consume(|c| c != '"');
                while let Some(c) = self.sc.peek() {
                    match c {
                        '\\' => {
                            if self.sc.next().is_none() {
                                return Some(Err(BadStringEscape));
                            }
                        }
                        '"' => {
                            break;
                        }
                        _ => (),
                    }
                }
                if self.sc.eat('"') {
                    Ok(Token::String)
                } else {
                    Err(ExpectedQuote)
                }
            }

            // Macro Replacement Ident
            '$' => {
                self.sc.consume(is_ident_later);
                Ok(Token::InlineCReplacementIdent)
            }

            // Macro Identifier
            '@' if self.sc.eat('.') => {
                if self.sc.eat('.') {
                    Ok(Token::AtDotDot)
                } else {
                    Err(UnexpectedCharacter('.'))
                }
            }
            '@' if self.sc.eat('@') => Ok(Token::AtAt),
            '@' => {
                self.sc.consume(is_ident_later);
                if self.sc.current() == "@c" {
                    Ok(Token::InlineCMacroIdent)
                } else {
                    Ok(Token::MacroIdent)
                }
            }

            // Numbers
            c if c.is_ascii_digit() => {
                self.sc.consume(|c| c.is_ascii_digit());
                if self.sc.peek() == Some('.') && self.sc.peek2() != Some('.') {
                    self.sc.next().unwrap();
                    self.sc.consume(|c| c.is_ascii_digit());
                    Ok(Token::Float)
                } else {
                    Ok(Token::Integer)
                }
            }

            // Finicky operators
            ':' if self.sc.eat(':') => Ok(Token::ColonColon), // '::'
            ':' => Ok(Token::Colon),                          // ':'
            '<' if self.sc.eat('<') => Ok(Token::LtLt),       // '<<'
            '<' if self.sc.eat('=') => Ok(Token::LtEq),       // '<='
            '<' => Ok(Token::Lt),                             // '<'
            '>' if self.sc.eat('>') => Ok(Token::GtGt),       // '>>'
            '>' if self.sc.eat('=') => Ok(Token::GtEq),       // '>=
            '>' => Ok(Token::Gt),                             // '>'
            ';' => Ok(Token::Semi),                           // ';'
            ',' => Ok(Token::Comma),                          // ','
            '(' => Ok(Token::OpenParen),                      // '('
            ')' => Ok(Token::CloseParen),                     // ')'
            '[' => Ok(Token::OpenBrack),                      // '['
            ']' => Ok(Token::CloseBrack),                     // ']'
            '{' => Ok(Token::OpenBrace),                      // '{'
            '}' => Ok(Token::CloseBrace),                     // '}'
            '~' => Ok(Token::Tilde),                          // '~'
            '=' if self.sc.eat('=') => Ok(Token::EqEq),       // '=='
            '=' => Ok(Token::Eq),                             // '='
            '!' if self.sc.eat('=') => Ok(Token::BangEq),     // '!='
            '!' => Ok(Token::Bang),                           // '!'
            '|' if self.sc.eat('|') => Ok(Token::BarBar),     // '||'
            '|' if self.sc.eat('=') => Ok(Token::BarBar),     // '|='
            '|' => Ok(Token::Bar),                            // '|'
            '&' if self.sc.eat('&') => Ok(Token::AndAnd),     // '&&'
            '&' if self.sc.eat('=') => Ok(Token::AndEq),      // '&='
            '&' => Ok(Token::And),                            // '&'
            '^' if self.sc.eat('=') => Ok(Token::CaretEq),    // '^='
            '^' => Ok(Token::Caret),                          // '^'
            '+' if self.sc.eat('=') => Ok(Token::PlusEq),     // '+='
            '+' => Ok(Token::Plus),                           // '+'
            '-' if self.sc.eat('=') => Ok(Token::MinusEq),    // '-='
            '-' if self.sc.eat('>') => Ok(Token::Arrow),      // '->'
            '-' => Ok(Token::Minus),                          // '-'
            '*' if self.sc.eat('=') => Ok(Token::StarEq),     // '*='
            '*' => Ok(Token::Star),                           // '*'
            '/' if self.sc.eat('=') => Ok(Token::SlashEq),    // '/='
            '/' => Ok(Token::Slash),                          // '/'
            '%' if self.sc.eat('=') => Ok(Token::PercentEq),  // '%='
            '%' => Ok(Token::Percent),                        // '%'
            '.' if self.sc.eat('.') => {
                if self.sc.eat('@') {
                    Ok(Token::DotDotAt) // '..@'
                } else {
                    Ok(Token::DotDot) // '..'
                }
            }
            '.' => Ok(Token::Dot), // '.'

            // Identifiers
            c if is_ident_first(c) => {
                self.sc.consume(is_ident_later);
                Ok(match_keyword(self.sc.current()).unwrap_or(Token::Ident))
            }

            // Whitespace
            c if c.is_whitespace() => {
                self.sc.consume(|c| c.is_whitespace());
                self.sc.skip();
                self.next_tok()?
            }
            _ => Err(UnexpectedCharacter(c)),
        };
        Some(result)
    }
}

impl<'input> Iterator for Lexer<'_> {
    type Item = Result<(usize, Token, usize), LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next_tok()? {
            Ok(token) => {
                let start = self.sc.start;
                let end = self.sc.end;
                self.sc.skip();
                Some(Ok((start, token, end)))
            }
            Err(e) => panic!("{:?}, '{}'", e, self.sc.current()),
            // Err(e) => Some(Err(e)),
        }
    }
}
