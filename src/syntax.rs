use chumsky::prelude::*;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    Integer(String),
    Identifier(String),
    LineComment(String),
    // Operators
    Operator(char), // 1 char
    // Keywords
    Def,
    End,
    Puts,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Integer(n) => write!(f, "{}", n),
            Token::Operator(c) => write!(f, "{}", c),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::LineComment(s) => write!(f, "# {}", s),
            Token::Def => write!(f, "def"),
            Token::End => write!(f, "end"),
            Token::Puts => write!(f, "puts"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let integer = text::int(10).map(Token::Integer);
    let operator = one_of("+-*/=(),").map(Token::Operator);
    let identifier = choice((
        text::keyword("def").to(Token::Def),
        text::keyword("end").to(Token::End),
        text::keyword("puts").to(Token::Puts),
        text::ident().map(Token::Identifier),
    ));

    let comment = just("#")
        .ignore_then(take_until(text::newline()))
        .map(|(chars, _)| chars.iter().collect::<String>())
        .map(Token::LineComment);

    let token = integer
        .or(operator)
        .or(identifier)
        .or(comment)
        .recover_with(skip_then_retry_until([]));

    token.padded().repeated().then_ignore(end())
}

#[derive(Debug)]
pub enum Expr {
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

    // Built-in functions
    Puts(Vec<Expr>),
}

pub fn parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    let op = |c| just(Token::Operator(c));
    let ident = select! {
        Token::Identifier(ident) => ident,
    }
    .labelled("identifier");

    let expr = recursive(|expr| {
        let value = select! {
            Token::Integer(n) => Expr::Integer(n.parse().unwrap()),
        }
        .labelled("value");

        let puts = just(Token::Puts)
            .ignore_then(
                expr.clone()
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(Token::Operator('('), Token::Operator(')')),
            )
            .map(Expr::Puts)
            .labelled("puts");

        let call = ident
            .then(
                expr.clone()
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(Token::Operator('('), Token::Operator(')')),
            )
            .map(|(f, args)| Expr::Call(f, args))
            .labelled("call");

        let atom = value
            .or(expr.delimited_by(Token::Operator('('), Token::Operator(')')))
            .or(puts)
            .or(call)
            .or(ident.map(Expr::Var));

        // unary: "-"
        let unary = op('-')
            .repeated()
            .then(atom)
            .foldr(|_op, rhs| Expr::Neg(Box::new(rhs)));

        // binary: "*", "/"
        let product = unary
            .clone()
            .then(
                op('*')
                    .to(Expr::Mul as fn(_, _) -> _)
                    .or(op('/').to(Expr::Div as fn(_, _) -> _))
                    .then(unary)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)));

        // binary: "+", "-"
        product
            .clone()
            .then(
                op('+')
                    .to(Expr::Add as fn(_, _) -> _)
                    .or(op('-').to(Expr::Sub as fn(_, _) -> _))
                    .then(product)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)))
    });

    let decl = recursive(|decl| {
        // Variable declaration
        let r#let = ident
            .then_ignore(op('='))
            .then(expr.clone())
            .then(decl.clone())
            .map(|((name, rhs), then)| Expr::Let {
                name,
                rhs: Box::new(rhs),
                then: Box::new(then),
            });

        // Function declaration
        let r#fn = just(Token::Def)
            .ignore_then(ident)
            .then(
                ident
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(Token::Operator('('), Token::Operator(')')),
            )
            .then(expr.clone())
            .then_ignore(just(Token::End))
            .then(decl)
            .map(|(((name, args), body), then)| Expr::Fn {
                name,
                args,
                body: Box::new(body),
                then: Box::new(then),
            });

        r#let.or(r#fn).or(expr)
    });

    decl.then_ignore(end())
}
