use chumsky::prelude::*;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Debug, Clone, Eq)]
pub struct Token {
    kind: TokenKind,
    // leading comments followed by this token.
    comments: Vec<String>,
    // a trailing comment which follows this token.
    trailing_comment: Option<String>,
}

impl Token {
    pub fn new(kind: TokenKind, comments: &[&str], trailing_comment: Option<&str>) -> Self {
        Self {
            kind,
            comments: comments.iter().map(ToString::to_string).collect(),
            trailing_comment: trailing_comment.map(ToString::to_string),
        }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn trailing_comment(&self) -> Option<&str> {
        self.trailing_comment.as_ref().map(AsRef::as_ref)
    }
}

// To work with chumsky parser combinator, Token equality ignores metadata like comments.
impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for comment in self.comments() {
            writeln!(f, "#{}", comment)?;
        }
        write!(f, "{}", self.kind)?;
        if let Some(comment) = self.trailing_comment() {
            write!(f, "  #{}", comment)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Integer(String),
    Identifier(String),
    // Operators
    Operator(char), // 1 char
    // Keywords
    Def,
    Case,
    When,
    Else,
    End,
    Puts,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TokenKind::Integer(n) => write!(f, "{}", n),
            TokenKind::Operator(c) => write!(f, "{}", c),
            TokenKind::Identifier(s) => write!(f, "{}", s),
            TokenKind::Def => write!(f, "def"),
            TokenKind::Case => write!(f, "case"),
            TokenKind::When => write!(f, "when"),
            TokenKind::Else => write!(f, "else"),
            TokenKind::End => write!(f, "end"),
            TokenKind::Puts => write!(f, "puts"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let integer = text::int(10).map(TokenKind::Integer);
    let operator = one_of("+-*/=(),").map(TokenKind::Operator);
    let identifier = choice((
        text::keyword("def").to(TokenKind::Def),
        text::keyword("case").to(TokenKind::Case),
        text::keyword("when").to(TokenKind::When),
        text::keyword("else").to(TokenKind::Else),
        text::keyword("end").to(TokenKind::End),
        text::keyword("puts").to(TokenKind::Puts),
        text::ident().map(TokenKind::Identifier),
    ));

    let token = integer
        .or(operator)
        .or(identifier)
        .recover_with(skip_then_retry_until([]));

    // whitespace except for newlines
    let whitespace = one_of(" \t").repeated();
    let comment = just("#")
        .ignore_then(take_until(text::newline()))
        .map(|(chars, _)| Some(chars.iter().collect::<String>()));

    // line comments followed by token
    let token_with_comments = comment
        .padded()
        .repeated()
        // token
        .then(token)
        // a trailing comment. It must exist one or not.
        .then_ignore(whitespace)
        .then(comment.or(empty().to(None)))
        .map(
            |((comments, kind), trailing_comment): (
                (Vec<Option<String>>, TokenKind),
                Option<String>,
            )| {
                let comments = comments
                    .iter()
                    .filter_map(|v| v.as_ref().map(AsRef::as_ref))
                    .collect::<Vec<&str>>();
                let trailing_comment = trailing_comment.as_ref().map(AsRef::as_ref);

                Token::new(kind, &comments, trailing_comment)
            },
        )
        .padded();

    token_with_comments
        .repeated()
        // Ignore trailing comments of the file.
        .then_ignore(comment.padded().repeated())
        .then_ignore(end())
}

#[derive(Debug)]
pub struct Expr {
    kind: ExprKind,
    // comments followed by this token.
    comments: Vec<String>,
    // a trailing comment which follows this token.
    trailing_comment: Option<String>,
}

impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Self {
            kind,
            comments: vec![],
            trailing_comment: None,
        }
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn trailing_comment(&self) -> Option<&str> {
        self.trailing_comment.as_ref().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub enum ExprKind {
    Integer(i64),
    Var(String),

    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    Call(String, Vec<Expr>),
    Let {
        name: String,
        rhs: Box<Expr>,
        then: Box<Expr>,
    },
    Fn {
        name: String,
        args: Vec<String>,
        body: Box<Expr>,
        then: Box<Expr>,
    },
    Case {
        head: Box<Expr>,
        arms: Vec<CaseArm>,
        else_body: Option<Box<Expr>>,
    },

    // Built-in functions
    Puts(Vec<Expr>),
}

#[derive(Debug)]
pub struct CaseArm {
    pattern: Pattern,
    body: Box<Expr>,
    comments: Vec<String>,
}

impl CaseArm {
    pub fn new(pattern: Pattern, body: Box<Expr>) -> Self {
        Self {
            pattern,
            body,
            comments: vec![],
        }
    }

    pub fn pattern(&self) -> &Pattern {
        &self.pattern
    }

    pub fn body(&self) -> &Expr {
        &self.body
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub struct Pattern {
    kind: PatternKind,
    comments: Vec<String>,
    trailing_comment: Option<String>,
}

impl Pattern {
    pub fn new(kind: PatternKind) -> Self {
        Self {
            kind,
            comments: vec![],
            trailing_comment: None,
        }
    }

    pub fn kind(&self) -> &PatternKind {
        &self.kind
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
    }

    pub fn trailing_comment(&self) -> Option<&str> {
        self.trailing_comment.as_ref().map(AsRef::as_ref)
    }

    pub fn append_comments_from(&mut self, token: &Token) {
        for comment in token.comments() {
            self.comments.push(comment.to_string());
        }
    }
}

#[derive(Debug)]
pub enum PatternKind {
    Integer(i64),
}

fn token(kind: TokenKind) -> Token {
    Token::new(kind, &[], None)
}

pub fn parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    let op = |c| just(token(TokenKind::Operator(c)));
    let ident = select! {
        Token{ kind: TokenKind::Identifier(ident), ..} => ident,
    }
    .labelled("identifier");

    let expr = recursive(|expr| {
        let value = select! {
            Token{ kind: TokenKind::Integer(n), ..} => {
                let kind = ExprKind::Integer(n.parse().unwrap());
                Expr::new(kind)
            },
        }
        .labelled("value");

        let puts = just(token(TokenKind::Puts))
            .ignore_then(
                expr.clone()
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(
                        token(TokenKind::Operator('(')),
                        token(TokenKind::Operator(')')),
                    ),
            )
            .map(|args| Expr::new(ExprKind::Puts(args)))
            .labelled("puts");

        let call = ident
            .then(
                expr.clone()
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(
                        token(TokenKind::Operator('(')),
                        token(TokenKind::Operator(')')),
                    ),
            )
            .map(|(f, args)| Expr::new(ExprKind::Call(f, args)))
            .labelled("call");

        let atom = value
            .or(expr.delimited_by(
                token(TokenKind::Operator('(')),
                token(TokenKind::Operator(')')),
            ))
            .or(puts)
            .or(call)
            .or(ident.map(|s| Expr::new(ExprKind::Var(s))));

        // unary: "-"
        let unary = op('-')
            .repeated()
            .then(atom)
            .foldr(|_op, rhs| Expr::new(ExprKind::Neg(Box::new(rhs))));

        // binary: "*", "/"
        let product = unary
            .clone()
            .then(
                op('*')
                    .to(ExprKind::Mul as fn(_, _) -> _)
                    .or(op('/').to(ExprKind::Div as fn(_, _) -> _))
                    .then(unary)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))));

        // binary: "+", "-"
        product
            .clone()
            .then(
                op('+')
                    .to(ExprKind::Add as fn(_, _) -> _)
                    .or(op('-').to(ExprKind::Sub as fn(_, _) -> _))
                    .then(product)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))))
    });

    let decl = recursive(|decl| {
        // Variable declaration
        let r#let = ident
            .then_ignore(op('='))
            .then(expr.clone())
            .then(decl.clone())
            .map(|((name, rhs), then)| {
                Expr::new(ExprKind::Let {
                    name,
                    rhs: Box::new(rhs),
                    then: Box::new(then),
                })
            });

        // Function declaration
        let r#fn = 
            // can not use "just" which outputs an argument instead of a token from the input.
            filter(|t: &Token| t.kind == TokenKind::Def)
            .then(ident)
            .then(ident.separated_by(op(',')).allow_trailing().delimited_by(
                token(TokenKind::Operator('(')),
                token(TokenKind::Operator(')')),
            ))
            .then(expr.clone())
            .then_ignore(just(token(TokenKind::End)))
            .then(decl)
            .map(|((((def_tok, name), args), body), then)| {
                let mut expr = Expr::new(ExprKind::Fn {
                    name,
                    args,
                    body: Box::new(body),
                    then: Box::new(then),
                });
                // Copy leading comments from "def" token
                expr.append_comments_from(&def_tok);
                expr
            });

        r#let.or(r#fn).or(expr)
    });

    decl.then_ignore(end())
}
