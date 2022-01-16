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
    LiteralString(String),
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
    // Types
    Int64,
    Boolean,
    String,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Integer(n) => write!(f, "{}", n),
            Self::Identifier(s) => write!(f, "`{}`", s),
            Self::LiteralString(s) => write!(f, "\"{}\"", s.escape_default().collect::<String>()),
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
            Self::Int64 => write!(f, "int64"),
            Self::Boolean => write!(f, "boolean"),
            Self::String => write!(f, "string"),
        }
    }
}

pub fn tokenize(src: &str) -> Result<Vec<Token>, Vec<Simple<char>>> {
    lexer().parse(src)
}

fn lexer() -> impl Parser<char, Vec<Token>, Error = Simple<char>> {
    let integer = text::int(10);
    let pos_integer = integer.map(TokenKind::Integer);
    let neg_integer = just('-')
        .ignore_then(integer)
        .map(|s| TokenKind::Integer(format!("-{}", s)));
    let integer = pos_integer.or(neg_integer);

    let operator1 = one_of("+-*/=(),<>:").map(TokenKind::Operator);
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
        text::keyword("int64").to(TokenKind::Int64),
        text::keyword("boolean").to(TokenKind::Boolean),
        text::keyword("string").to(TokenKind::String),
        text::ident().map(TokenKind::Identifier),
    ));

    // string
    let escape = just('\\').ignore_then(
        just('\\')
            .or(just('/'))
            .or(just('"'))
            .or(just('b').to('\x08'))
            .or(just('f').to('\x0C'))
            .or(just('n').to('\n'))
            .or(just('r').to('\r'))
            .or(just('t').to('\t')),
    );

    let string = just('"')
        .ignore_then(filter(|c| *c != '\\' && *c != '"').or(escape).repeated())
        .then_ignore(just('"'))
        .collect::<String>()
        .map(TokenKind::LiteralString)
        .labelled("string");

    let token = integer
        .or(identifier)
        .or(string)
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
