use std::fmt;

use crate::ty::{FunctionSignature, Type};
use thiserror::Error;

#[derive(Debug)]
pub struct FormatSymbols {
    pub names: Vec<String>,
}

impl fmt::Display for FormatSymbols {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut it = self.names.iter().peekable();

        while let Some(name) = it.next() {
            write!(f, "`{}`", name)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SemanticError<'tcx> {
    #[error("cannot find variable `{name}` in scope")]
    UndefinedVariable { name: String },
    #[error("cannot find function `{name}` in scope")]
    UndefinedFunction { name: String },
    #[error("cannot find named type `{name}` in scope")]
    UndefinedNamedType { name: String },
    #[error("cannot find named field `{name}` in `{struct_ty}`")]
    UndefinedStructField {
        name: String,
        struct_ty: &'tcx Type<'tcx>,
    },
    #[error("named field `{name}` is defined more than once in `{struct_ty}`")]
    DuplicateStructField {
        name: String,
        struct_ty: &'tcx Type<'tcx>,
    },
    #[error("function `{signature}` is defined more than once in the same scope")]
    DuplicateFunction { signature: FunctionSignature<'tcx> },
    #[error("named type `{name}` is bound more than once in the same scope")]
    DuplicateNamedType { name: String },
    #[error(
        "wrong number of arguments for function `{name}`: expected {expected}, found {actual}"
    )]
    WrongNumberOfArguments {
        name: String,
        expected: usize,
        actual: usize,
    },
    #[error("multiple candidate functions in overload resolution: {description}")]
    MultipleCandidateFunctions { description: String },
    // Type errors
    #[error("expected type `{expected}`, found `{actual}`")]
    MismatchedType {
        expected: &'tcx Type<'tcx>,
        actual: &'tcx Type<'tcx>,
    },
    #[error(
        "return type of function `{signature}` is specified with `{expected}`, found `{actual}`"
    )]
    MismatchedReturnType {
        signature: FunctionSignature<'tcx>,
        expected: &'tcx Type<'tcx>,
        actual: &'tcx Type<'tcx>,
    },
    #[error("return type of function `{signature}` cannot be inferred.")]
    UnrecognizedReturnType { signature: FunctionSignature<'tcx> },
    #[error("no field `{name}` on type `{ty}`")]
    FieldNotFound { name: String, ty: &'tcx Type<'tcx> },
    // pattern match errors
    #[error("uncovered fields {names} in struct pattern `{struct_ty}`")]
    UncoveredStructFields {
        names: FormatSymbols,
        struct_ty: &'tcx Type<'tcx>,
    },
    #[error("unreachable pattern: `{pattern}`")]
    UnreachablePattern { pattern: String },
    #[error("unreachable `else` clause")]
    UnreachableElseClause,
    #[error("non-exhaustive pattern: `{pattern}`")]
    NonExhaustivePattern { pattern: String },
    #[error("identifier `{name}` is bound more than once in the same pattern")]
    AlreadyBoundInPattern { name: String },
    #[error("spread pattern can appear only once: `{pattern}`")]
    DuplicateSpreadPattern { pattern: String },
    #[error("empty spread expression is no-op")]
    EmptySpreadExpression,
    #[error("value of `{ty}` cannot be spread")]
    InvalidSpreadOperand { ty: &'tcx Type<'tcx> },
    #[error("variable `{name}` is not bound in all patterns")]
    UnboundVariableInSubPattern { name: String },
}
