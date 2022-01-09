use chumsky::prelude::*;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Copy, Clone, PartialEq, Debug)]
pub enum RangeEnd {
    Included, // "..=" taken from Rust language
    Excluded, // "..<" taken from Swift language
}

impl fmt::Display for RangeEnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            RangeEnd::Included => "..=",
            RangeEnd::Excluded => "..<",
        })
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Token {
    kind: TokenKind,
    // Leading comments followed by this token.
    // For simplicity, we don't handle trailing comments. For example,
    // if we have a code like below:
    //
    //     # comment 1
    //     x = 1 # comment 2
    //     y = 2
    //
    // The "comment 1" will be the leading comment of "x" token, and
    // the "comment 2" will be "y" token's.
    comments: Vec<String>,
}

impl Token {
    pub fn new(kind: TokenKind, comments: &[&str]) -> Self {
        Self {
            kind,
            comments: comments.iter().map(ToString::to_string).collect(),
        }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn comments(&self) -> impl Iterator<Item = &str> {
        self.comments.iter().map(AsRef::as_ref)
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
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Integer(String),
    Identifier(String),
    // Operators
    RangeIncluded, // RangeEnd::Included
    RangeExcluded, // RangeEnd::Excluded
    Eq,
    Ne,
    Le,
    Ge,
    And,
    Or,
    Operator(char), // 1 char
    // Keywords
    Def,
    Case,
    When,
    Else,
    End,
    Puts,
    True,
    False,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Integer(n) => write!(f, "{}", n),
            Self::Identifier(s) => write!(f, "{}", s),
            Self::RangeIncluded => write!(f, "{}", RangeEnd::Included),
            Self::RangeExcluded => write!(f, "{}", RangeEnd::Excluded),
            Self::Operator(c) => write!(f, "{}", c),
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Le => write!(f, "<="),
            Self::Ge => write!(f, ">="),
            Self::And => write!(f, "&&"),
            Self::Or => write!(f, "||"),
            Self::Def => write!(f, "def"),
            Self::Case => write!(f, "case"),
            Self::When => write!(f, "when"),
            Self::Else => write!(f, "else"),
            Self::End => write!(f, "end"),
            Self::Puts => write!(f, "puts"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
        }
    }
}

pub fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let integer = text::int(10);
    let pos_integer = integer.map(TokenKind::Integer);
    let neg_integer = just('-')
        .ignore_then(integer)
        .map(|s| TokenKind::Integer(format!("-{}", s)));
    let integer = pos_integer.or(neg_integer);

    let operator1 = one_of("+-*/=(),<>").map(TokenKind::Operator);
    let operator2 = choice((
        just("..=").to(TokenKind::RangeIncluded),
        just("..<").to(TokenKind::RangeExcluded),
        just("==").to(TokenKind::Eq),
        just("!=").to(TokenKind::Ne),
        just("<=").to(TokenKind::Le),
        just(">=").to(TokenKind::Ge),
        just("&&").to(TokenKind::And),
        just("||").to(TokenKind::Or),
    ));
    let identifier = choice((
        text::keyword("def").to(TokenKind::Def),
        text::keyword("case").to(TokenKind::Case),
        text::keyword("when").to(TokenKind::When),
        text::keyword("else").to(TokenKind::Else),
        text::keyword("end").to(TokenKind::End),
        text::keyword("puts").to(TokenKind::Puts),
        text::keyword("true").to(TokenKind::True),
        text::keyword("false").to(TokenKind::False),
        text::ident().map(TokenKind::Identifier),
    ));

    let token = integer
        .or(identifier)
        .or(operator2)
        .or(operator1)
        .recover_with(skip_then_retry_until([]));

    let comment = just("#")
        .ignore_then(take_until(text::newline()))
        .map(|(chars, _)| Some(chars.iter().collect::<String>()));

    // line comments and token
    let token_with_comments = comment
        .padded()
        .repeated()
        .then(token)
        .map(|(comments, kind): (Vec<Option<String>>, TokenKind)| {
            let comments = comments
                .iter()
                .filter_map(|v| v.as_ref().map(AsRef::as_ref))
                .collect::<Vec<&str>>();

            Token::new(kind, &comments)
        })
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
}

impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Self {
            kind,
            comments: vec![],
        }
    }

    pub fn kind(&self) -> &ExprKind {
        &self.kind
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
pub enum ExprKind {
    Integer(i64),
    Boolean(bool),
    Var(String),

    // unary operators
    Minus(Box<Expr>),

    // binary operators
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Ne(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),

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
}

impl Pattern {
    pub fn new(kind: PatternKind) -> Self {
        Self {
            kind,
            comments: vec![],
        }
    }

    pub fn kind(&self) -> &PatternKind {
        &self.kind
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
pub enum PatternKind {
    Integer(i64),
    Boolean(bool),
    Range { lo: i64, hi: i64, end: RangeEnd },
    Wildcard,
}

impl fmt::Display for PatternKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PatternKind::Integer(n) => write!(f, "{}", n),
            PatternKind::Boolean(b) => write!(f, "{}", b),
            PatternKind::Range { lo, hi, end } => {
                if *lo == i64::MIN {
                    write!(f, "int64::MIN")?;
                } else {
                    write!(f, "{}", lo)?;
                }

                write!(f, "{}", end)?;

                if *hi == i64::MAX {
                    write!(f, "int64::MAX")
                } else {
                    write!(f, "{}", hi)
                }
            }
            PatternKind::Wildcard => write!(f, "_"),
        }
    }
}

fn token(kind: TokenKind) -> Token {
    Token::new(kind, &[])
}

pub fn parser() -> impl Parser<Token, Expr, Error = Simple<Token>> + Clone {
    // can not use "just" which outputs an argument instead of a token from the input.
    let just_token =
        |kind: TokenKind| filter::<Token, _, Simple<Token>>(move |t: &Token| t.kind == kind);

    let op = |c| just_token(TokenKind::Operator(c));

    let ident_value = select! {
        Token{ kind: TokenKind::Identifier(ident), ..} => ident,
    }
    .labelled("identifier");

    let integer_value = select! {
        Token{ kind: TokenKind::Integer(n), ..} => n.parse().unwrap()
    }
    .labelled("integer");

    let boolean_value = choice((
        just_token(TokenKind::True).to(true),
        just_token(TokenKind::False).to(false),
    ))
    .labelled("boolean");

    let pattern = {
        let integer_pattern = integer_value.map(|n| {
            let kind = PatternKind::Integer(n);
            Pattern::new(kind)
        });
        let boolean_pattern = boolean_value.clone().map(|b| {
            let kind = PatternKind::Boolean(b);
            Pattern::new(kind)
        });
        let range_pattern = integer_value
            .then(choice((
                just_token(TokenKind::RangeExcluded),
                just_token(TokenKind::RangeIncluded),
            )))
            .then(integer_value)
            .map(|((lhs, op), rhs)| {
                let end = if let TokenKind::RangeIncluded = op.kind() {
                    RangeEnd::Included
                } else {
                    RangeEnd::Excluded
                };

                let kind = PatternKind::Range {
                    lo: lhs,
                    hi: rhs,
                    end,
                };

                Pattern::new(kind)
            });

        range_pattern.or(integer_pattern).or(boolean_pattern)
    };

    let expr = recursive(|expr| {
        let integer = integer_value
            .map(|n| {
                let kind = ExprKind::Integer(n);
                Expr::new(kind)
            })
            .labelled("integer");

        let ident = ident_value
            .map(|s| Expr::new(ExprKind::Var(s)))
            .labelled("ident");

        let boolean = boolean_value
            .map(|b| Expr::new(ExprKind::Boolean(b)))
            .labelled("boolean");

        let puts = just_token(TokenKind::Puts)
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

        let call = ident_value
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

        let atom = expr
            .clone()
            .delimited_by(
                token(TokenKind::Operator('(')),
                token(TokenKind::Operator(')')),
            )
            .or(integer)
            .or(boolean)
            .or(puts)
            .or(call)
            .or(ident);

        // unary: "-"
        let unary = op('-')
            .repeated()
            .then(atom)
            .foldr(|_op, rhs| Expr::new(ExprKind::Minus(Box::new(rhs))));

        // binary: "*", "/"
        let bin_op1 = unary
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
        let bin_op2 = bin_op1
            .clone()
            .then(
                op('+')
                    .to(ExprKind::Add as fn(_, _) -> _)
                    .or(op('-').to(ExprKind::Sub as fn(_, _) -> _))
                    .then(bin_op1)
                    .repeated(),
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))));

        // comparison operators
        #[rustfmt::skip]
        let comp_op = bin_op2
            .clone()
            .then(
                op('<').to(ExprKind::Lt as fn(_, _) -> _).or(
                op('>').to(ExprKind::Gt as fn(_, _) -> _).or(
                just_token(TokenKind::Le).to(ExprKind::Le as fn(_, _) -> _).or(
                just_token(TokenKind::Ge).to(ExprKind::Ge as fn(_, _) -> _)
            )))
                .then(bin_op2).repeated().at_most(1)
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))));

        // equality operators
        #[rustfmt::skip]
        let eq_op = comp_op
            .clone()
            .then(
                just_token(TokenKind::Eq).to(ExprKind::Eq as fn(_, _) -> _).or(
                just_token(TokenKind::Ne).to(ExprKind::Ne as fn(_, _) -> _)
            )
                .then(comp_op).repeated().at_most(1)
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))));

        // logical operators
        #[rustfmt::skip]
        let logical_op = eq_op
            .clone()
            .then(
                just_token(TokenKind::And).to(ExprKind::And as fn(_, _) -> _).or(
                just_token(TokenKind::Or).to(ExprKind::Or as fn(_, _) -> _)
            )
                .then(eq_op).repeated().at_most(1)
            )
            .foldl(|lhs, (op, rhs)| Expr::new(op(Box::new(lhs), Box::new(rhs))));

        // case
        let case_arm = just_token(TokenKind::When)
            .then(pattern)
            .then(expr.clone())
            .map(|((when, pattern), body)| {
                let mut expr = CaseArm::new(pattern, Box::new(body));
                expr.append_comments_from(&when);
                expr
            });
        let case = just_token(TokenKind::Case)
            .then(expr.clone())
            .then(case_arm.repeated().at_least(1))
            .then(just_token(TokenKind::Else).then(expr.clone()).or_not())
            .then_ignore(just_token(TokenKind::End))
            .map(|(((case, head), arms), else_body)| {
                let else_body = else_body.map(|(_else_tok, expr)| Box::new(expr));

                let mut expr = Expr::new(ExprKind::Case {
                    head: Box::new(head),
                    arms,
                    else_body,
                });
                expr.append_comments_from(&case);
                expr
            });

        case.or(logical_op)
    });

    let decl = recursive(|decl| {
        // Variable declaration
        let r#let = ident_value
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
        let r#fn = just_token(TokenKind::Def)
            .then(ident_value)
            .then(
                ident_value
                    .separated_by(op(','))
                    .allow_trailing()
                    .delimited_by(
                        token(TokenKind::Operator('(')),
                        token(TokenKind::Operator(')')),
                    ),
            )
            .then(expr.clone())
            .then_ignore(just_token(TokenKind::End))
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
