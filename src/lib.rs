use chumsky::prelude::*;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    Integer(String),
    Identifier(String),
    // Operators
    Operator(char), // 1 char
    // Keywords
    Def,
    End,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Integer(n) => write!(f, "{}", n),
            Token::Operator(c) => write!(f, "{}", c),
            Token::Identifier(s) => write!(f, "{}", s),
            Token::Def => write!(f, "def"),
            Token::End => write!(f, "end"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let integer = text::int(10).map(Token::Integer);
    let operator = one_of("+-*/=(),").map(Token::Operator);
    let identifier = text::ident().map(|ident: String| match ident.as_str() {
        "def" => Token::Def,
        "end" => Token::End,
        _ => Token::Identifier(ident),
    });

    let token = integer
        .or(operator)
        .or(identifier)
        .recover_with(skip_then_retry_until([]));

    let comment = just("#").then(take_until(just('\n'))).padded();

    token.padded_by(comment.repeated()).padded().repeated()
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
}

pub fn parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    let op = |c| just(Token::Operator(c));
    let ident = filter_map(|span, tok| match tok {
        Token::Identifier(ident) => Ok(ident),
        _ => Err(Simple::expected_input_found(span, Vec::new(), Some(tok))),
    })
    .labelled("identifier");

    let expr = recursive(|expr| {
        let value = filter_map(|span, tok| match tok {
            Token::Integer(n) => Ok(Expr::Integer(n.parse().unwrap())),
            _ => Err(Simple::expected_input_found(span, Vec::new(), Some(tok))),
        })
        .labelled("value");

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

pub fn eval(expr: &Expr) -> Result<i64, String> {
    eval_loop(expr, &mut Vec::new(), &mut Vec::new())
}

fn eval_loop<'a>(
    expr: &'a Expr,
    vars: &mut Vec<(&'a String, i64)>,
    functions: &mut Vec<(&'a String, &'a [String], &'a Expr)>,
) -> Result<i64, String> {
    match expr {
        Expr::Integer(x) => Ok(*x),
        Expr::Neg(a) => Ok(-eval_loop(a, vars, functions)?),
        Expr::Add(a, b) => Ok(eval_loop(a, vars, functions)? + eval_loop(b, vars, functions)?),
        Expr::Sub(a, b) => Ok(eval_loop(a, vars, functions)? - eval_loop(b, vars, functions)?),
        Expr::Mul(a, b) => Ok(eval_loop(a, vars, functions)? * eval_loop(b, vars, functions)?),
        Expr::Div(a, b) => Ok(eval_loop(a, vars, functions)? / eval_loop(b, vars, functions)?),
        Expr::Var(name) => {
            if let Some((_, val)) = vars.iter().rev().find(|(var, _)| *var == name) {
                Ok(*val)
            } else {
                Err(format!("Cannot find variable `{}` in scope", name))
            }
        }
        Expr::Let { name, rhs, then } => {
            let rhs = eval_loop(rhs, vars, functions)?;
            vars.push((name, rhs));
            let output = eval_loop(then, vars, functions);
            vars.pop();
            output
        }
        Expr::Call(name, args) => {
            if let Some((_, arg_names, body)) = functions
                .iter()
                .rev()
                .find(|(var, _, _)| *var == name)
                .copied()
            {
                if arg_names.len() == args.len() {
                    let mut args = args
                        .iter()
                        .map(|arg| eval_loop(arg, vars, functions))
                        .zip(arg_names.iter())
                        .map(|(val, name)| Ok((name, val?)))
                        .collect::<Result<_, String>>()?;
                    vars.append(&mut args);
                    let output = eval_loop(body, vars, functions);
                    vars.truncate(vars.len() - args.len());
                    output
                } else {
                    Err(format!(
                        "Wrong number of arguments for function `{}`: expected {}, found {}",
                        name,
                        arg_names.len(),
                        args.len(),
                    ))
                }
            } else {
                Err(format!("Cannot find function `{}` in scope", name))
            }
        }
        Expr::Fn {
            name,
            args,
            body,
            then,
        } => {
            functions.push((name, args, body));
            let output = eval_loop(then, vars, functions);
            functions.pop();
            output
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn number() {
        let val = eval_i64("20211231");
        assert_eq!(val, 20211231);
    }

    #[test]
    fn variable() {
        let val = eval_i64(
            "
            five = 5
            five",
        );
        assert_eq!(val, 5);
    }

    #[test]
    fn function() {
        let val = eval_i64(
            "
            def foo(x, y)
                x + y
            end
            foo(10, 20)",
        );
        assert_eq!(val, 30);
    }

    fn eval_i64(src: &str) -> i64 {
        let tokens = lexer().parse(src).unwrap();
        let ast = parser().parse(tokens).unwrap();

        eval(&ast).unwrap()
    }
}
