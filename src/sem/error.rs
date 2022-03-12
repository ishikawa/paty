use crate::ty::{FunctionSignature, StructTy, Type};
use std::fmt;
use thiserror::Error;

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct SemanticError<'tcx> {
    kind: SemanticErrorKind<'tcx>,
    // TODO: Replace with location information (line and column).
    /// the information where the error occurred.
    location: String,
}

impl<'tcx> SemanticError<'tcx> {
    pub fn new(kind: SemanticErrorKind<'tcx>, location: String) -> Self {
        Self { kind, location }
    }

    pub fn from_kind(kind: SemanticErrorKind<'tcx>) -> Self {
        Self::new(kind, "".to_string())
    }

    pub fn kind(&self) -> &SemanticErrorKind<'tcx> {
        &self.kind
    }

    pub fn location(&self) -> &str {
        &self.location
    }
}

impl fmt::Display for SemanticError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.location.is_empty() {
            write!(f, "{}", self.kind)
        } else {
            write!(f, "{} at `{}`", self.kind, self.location)
        }
    }
}

#[derive(Error, Debug, Clone)]
pub enum SemanticErrorKind<'tcx> {
    #[error("cannot find variable `{name}` in scope")]
    UndefinedVariable { name: String },
    #[error("cannot find function `{name}` in scope")]
    UndefinedFunction { name: String },
    #[error("cannot find named type `{name}` in scope")]
    UndefinedNamedType { name: String },
    #[error("cannot find named field `{name}` in `{struct_ty}`")]
    UndefinedStructField {
        name: String,
        struct_ty: &'tcx StructTy<'tcx>,
    },
    #[error("anonymous struct cannot be initialized with type alias `{alias}`")]
    InitializeAnonymousStructWithTypeAlias { alias: String },
    #[error("no field `{name}` on type `{ty}`")]
    FieldNotFound { name: String, ty: &'tcx Type<'tcx> },
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
