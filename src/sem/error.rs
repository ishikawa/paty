use crate::ty::Type;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SemanticError<'tcx> {
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
    // Type errors
    #[error("expected type `{expected}`, found `{actual}`")]
    MismatchedType {
        expected: &'tcx Type<'tcx>,
        actual: &'tcx Type<'tcx>,
    },
    #[error("no field `{name}` on type `{ty}`")]
    FieldNotFound { name: String, ty: &'tcx Type<'tcx> },
    // pattern match errors
    #[error("unreachable pattern: `{pattern}`")]
    UnreachablePattern { pattern: String },
    #[error("unreachable `else` clause")]
    UnreachableElseClause,
    #[error("non-exhaustive pattern: `{pattern}`")]
    NonExhaustivePattern { pattern: String },
    #[error("identifier `{name}` is bound more than once in the same pattern")]
    AlreadyBoundInPattern { name: String },
    #[error("named type `{name}` is bound more than once in the same scope")]
    DuplicateNamedType { name: String },
    #[error("cannot find named type `{name}` in scope")]
    UndefinedNamedType { name: String },
}
