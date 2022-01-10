//! C code generator
use crate::typing::Type;

use super::ir::{Expr, Function, Program, Stmt, Value};

#[derive(Debug)]
pub struct Emitter {}

impl<'a> Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Emitter {
    pub fn new() -> Self {
        Self {}
    }

    pub fn emit(&mut self, program: &'a Program<'a>) -> String {
        let mut code = [
            "#include <stdio.h>",
            "#include <stdint.h>",
            "#include <stdbool.h>",
            "#include <inttypes.h>",
            "\n",
        ]
        .join("\n");

        for fun in &program.functions {
            self.emit_function(fun, &mut code);
            code.push('\n');
        }

        code
    }

    fn emit_function(&mut self, fun: &Function<'a>, code: &mut String) {
        if fun.is_entry_point {
            // 'main' must return 'int'
            code.push_str("int");
        } else {
            code.push_str(native_ty(Type::Int64));
        }
        code.push(' ');

        code.push_str(&fun.name);
        code.push('(');
        for (i, param) in fun.params.iter().enumerate() {
            code.push_str(native_ty(param.ty));
            code.push(' ');
            code.push_str(&param.name);

            if i != (fun.params.len() - 1) {
                code.push_str(", ");
            }
        }
        code.push_str(")\n");

        // body
        code.push_str("{\n");
        for stmt in &fun.body {
            self.emit_stmt(stmt, code);
        }
        code.push_str("}\n");
    }

    fn emit_stmt(&mut self, stmt: &Stmt<'a>, code: &mut String) {
        match stmt {
            Stmt::TmpVarDef { var, init, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str("int64_t ");
                        code.push_str(&format!("t{} = ", var.index));
                    }
                    self.emit_expr(init, code);
                    code.push_str(";\n");
                }
            }
            Stmt::VarDef { name, init } => {
                code.push_str("int64_t ");
                code.push_str(name);
                code.push_str(" = ");
                self.emit_expr(init, code);
                code.push_str(";\n");
            }
            Stmt::Ret(expr) => {
                code.push_str("return ");
                self.emit_expr(expr, code);
                code.push_str(";\n");
            }
            Stmt::Phi { var, value, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str(&format!("t{} = ", var.index));
                    }
                    self.emit_expr(value, code);
                    code.push_str(";\n");
                }
            }
            Stmt::Cond { branches, var } => {
                if var.used.get() > 0 {
                    code.push_str("int64_t ");
                    code.push_str(&format!("t{}", var.index));
                    code.push_str(";\n");
                }

                // Construct "if-else" statement from each branches.
                for (i, branch) in branches.iter().enumerate() {
                    if i > 0 {
                        code.push_str("else ");
                    }

                    if let Some(condition) = branch.condition {
                        code.push_str("if (");
                        self.emit_expr(condition, code);
                        code.push_str(") ");
                    }

                    // body
                    code.push_str("{\n");
                    for stmt in &branch.body {
                        self.emit_stmt(stmt, code);
                    }
                    code.push_str("}\n");
                }
            }
        }
    }

    fn emit_expr(&mut self, expr: &Expr<'a>, code: &mut String) {
        match expr {
            Expr::Minus(operand) => {
                code.push('-');
                self.emit_expr(operand, code);
            }
            Expr::Not(operand) => {
                code.push('!');
                self.emit_expr(operand, code);
            }
            Expr::Add(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" + ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Sub(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" - ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Mul(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" * ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Div(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" / ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Lt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" < ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Le(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" <= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Gt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" > ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Ge(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" >= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Eq(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" == ");
                self.emit_expr(rhs, code);
            }
            Expr::Ne(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" != ");
                self.emit_expr(rhs, code);
            }
            Expr::And(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" && ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Or(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" || ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            Expr::Call { name, args } => {
                code.push_str(&format!("{}(", name));
                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            Expr::Printf { args } => {
                code.push_str("printf(\"");
                for (i, arg) in args.iter().enumerate() {
                    // TODO: type inference

                    if let Expr::Value(Value::Bool(_)) = immediate(arg) {
                        // "true" / "false"
                        code.push_str("%s");
                    } else {
                        // Use standard conversion specifier macros for integer types.
                        code.push_str("%\" PRId64 \"");
                    }

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push_str("\\n\", ");

                for (i, arg) in args.iter().enumerate() {
                    // TODO: type inference

                    if let Expr::Value(Value::Bool(_)) = immediate(arg) {
                        // "true" / "false"
                        code.push('(');
                        self.emit_expr(arg, code);
                        code.push_str(" ? \"true\" : \"false\"");
                        code.push(')');
                    } else {
                        self.emit_expr(arg, code);
                    }

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            Expr::Value(value) => self.emit_value(value, code),
        }
    }

    fn emit_value(&mut self, value: &Value, code: &mut String) {
        match value {
            Value::Int(n) => code.push_str(&format!("{}", *n)),
            Value::Int64(n) =>
            // Use standard macros for integer constant expression to expand
            // a value to the type int_least_N.
            {
                code.push_str(&format!("INT64_C({})", *n))
            }
            Value::Bool(b) =>
            // Use standard macros for boolean constant expression.
            {
                if *b {
                    code.push_str("true");
                } else {
                    code.push_str("false");
                }
            }
            Value::TmpVar(t) => {
                if let Some(expr) = t.immediate.get() {
                    self.emit_expr(expr, code);
                } else {
                    code.push_str(&format!("t{}", t.index));
                }
            }
            Value::Var(name) => code.push_str(name),
        }
    }
}

fn immediate<'a>(expr: &'a Expr<'a>) -> &'a Expr<'a> {
    if let Expr::Value(Value::TmpVar(t)) = expr {
        if let Some(expr) = t.immediate.get() {
            return expr;
        }
    }
    expr
}

fn native_ty(ty: Type) -> &'static str {
    match ty {
        Type::Int64 => "int64_t",
        Type::Boolean => "bool",
    }
}
