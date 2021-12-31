//! C code generator
use crate::sem;
use crate::syntax;

#[derive(Debug, Default)]
struct Emitter {
    main: String,
    functions: Vec<String>,
}

impl Emitter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn emit(&self) -> String {
        ["#include <stdio.h>", &self.functions.join("\n"), &self.main].join("\n")
    }

    pub fn build(&self, _expr: &syntax::Expr) {}
}

pub fn emit(ast: &sem::SemAST) -> String {
    let emitter = Emitter::new();

    emitter.build(ast.expr());
    emitter.emit()
}
