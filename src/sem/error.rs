use thiserror::Error;

#[derive(Error, Debug)]
pub enum SemanticError {
    #[error("cannot find variable `{name}` in scope")]
    UndefinedVariable { name: String },
    #[error("cannot find function `{name}` in scope")]
    UndefinedFunction { name: String },
    #[error(
        "wrong number of arguments for function `{name}`: expected {expected}, found {actual}"
    )]
    WrongNumberOfArguments {
        name: String,
        expected: usize,
        actual: usize,
    },
    // pattern match errors
    #[error("unreachable pattern: `{pattern}`")]
    UnreachablePattern { pattern: String },
    #[error("non-exhaustive pattern: `{pattern}`")]
    NonExhaustivePattern { pattern: String },
}
