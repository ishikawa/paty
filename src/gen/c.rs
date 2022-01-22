//! C code generator
use crate::ty::Type;

use super::ir::{Expr, ExprKind, Function, LiteralStr, Program, Stmt, Value};

#[derive(Debug)]
pub struct Emitter {}

impl Default for Emitter {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, 'tcx> Emitter {
    pub fn new() -> Self {
        Self {}
    }

    pub fn emit(&mut self, program: &'a Program<'a, 'tcx>) -> String {
        let mut code = [
            "#include <stdio.h>",
            "#include <stdint.h>",
            "#include <stdbool.h>",
            "#include <inttypes.h>",
            "#include <string.h>",
            "\n",
        ]
        .join("\n");

        for ty in program.decl_types() {
            self.emit_decl_type(ty, &mut code);
            code.push('\n');
            code.push('\n');
        }

        for fun in program.functions() {
            self.emit_function(fun, &mut code);
            code.push('\n');
        }

        code
    }

    fn emit_decl_type(&mut self, ty: &Type<'tcx>, code: &mut String) {
        match ty {
            Type::Tuple(fs) => {
                code.push_str(&c_type(ty));
                code.push_str(" {\n");
                for (i, fty) in fs.iter().enumerate() {
                    code.push_str(&c_type(fty));
                    code.push(' ');
                    code.push_str(&format!("_{};\n", i));
                }
                code.push_str("};");
            }
            Type::Int64 | Type::Boolean | Type::String | Type::NativeInt => {
                unreachable!("invalid type for declaration type: {}", ty);
            }
        }
    }

    fn emit_function(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
        if fun.is_entry_point {
            // 'main' must return 'int'
            code.push_str(&c_type(&Type::NativeInt));
        } else {
            code.push_str(&c_type(fun.retty));
        }
        code.push(' ');

        code.push_str(&fun.name);
        code.push('(');
        for (i, param) in fun.params.iter().enumerate() {
            code.push_str(&c_type(param.ty));
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

    fn emit_stmt(&mut self, stmt: &Stmt<'a, 'tcx>, code: &mut String) {
        match stmt {
            Stmt::TmpVarDef { var, init, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str(&c_type(init.ty()));
                        code.push(' ');
                        code.push_str(&format!("t{} = ", var.index));
                    }
                    self.emit_expr(init, code);
                    code.push_str(";\n");
                }
            }
            Stmt::VarDef { name, init } => {
                code.push_str(&c_type(init.ty()));
                code.push(' ');
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
                    code.push_str(&c_type(var.ty));
                    code.push(' ');
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

    fn emit_expr(&mut self, expr: &Expr<'a, 'tcx>, code: &mut String) {
        match expr.kind() {
            ExprKind::Minus(operand) => {
                code.push('-');
                self.emit_expr(operand, code);
            }
            ExprKind::Not(operand) => {
                code.push('!');
                self.emit_expr(operand, code);
            }
            ExprKind::Add(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" + ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Sub(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" - ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Mul(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" * ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Div(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" / ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Lt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" < ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Le(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" <= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Gt(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" > ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Ge(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" >= ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Eq(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" == ");
                self.emit_expr(rhs, code);
            }
            ExprKind::Ne(lhs, rhs) => {
                self.emit_expr(lhs, code);
                code.push_str(" != ");
                self.emit_expr(rhs, code);
            }
            ExprKind::And(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" && ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Or(lhs, rhs) => {
                code.push('(');
                self.emit_expr(lhs, code);
                code.push_str(" || ");
                self.emit_expr(rhs, code);
                code.push(')');
            }
            ExprKind::Call { name, args } => {
                code.push_str(&format!("{}(", name));
                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            ExprKind::Select {
                condition,
                then_expr,
                else_expr,
            } => {
                code.push('(');
                self.emit_expr(condition, code);
                code.push_str(" ? ");
                self.emit_expr(then_expr, code);
                code.push_str(" : ");
                self.emit_expr(else_expr, code);
                code.push(')');
            }
            ExprKind::Value(value) => self.emit_value(value, code),
        }
    }

    fn emit_value(&mut self, value: &Value, code: &mut String) {
        match value {
            Value::Int(n) => code.push_str(&format!("{}", *n)),
            Value::Int64(n) => {
                // Use standard macros for integer constant expression to expand
                // a value to the type int_least_N.
                code.push_str(&format!("INT64_C({})", *n))
            }
            Value::Bool(b) => {
                // Use standard macros for boolean constant expression.
                if *b {
                    code.push_str("true");
                } else {
                    code.push_str("false");
                }
            }
            Value::LiteralStr(lits) => {
                let mut it = lits.iter().peekable();

                // concatenate adjusting literal string
                while let Some(lit) = it.peek() {
                    match lit {
                        LiteralStr::Str(_) => {
                            code.push_str("u8\"");
                            while let Some(LiteralStr::Str(s)) = it.peek() {
                                for c in s.escape_default() {
                                    code.push(c);
                                }
                                it.next();
                            }
                            code.push('"');
                        }
                        LiteralStr::Macro(m) => {
                            code.push_str(m);
                            it.next();
                        }
                    };

                    if it.peek().is_some() {
                        code.push(' ');
                    }
                }
            }
            Value::Tuple(ty, values) => {
                // Specify struct type explicitly.
                code.push('(');
                code.push_str(&c_type(ty));
                code.push(')');

                // Initialize tuple struct with designated initializers.
                code.push('{');

                let mut peekable = values.iter().enumerate().peekable();

                while let Some((i, value)) = peekable.next() {
                    code.push_str(&format!("._{} = ", i));
                    self.emit_expr(value, code);

                    if peekable.peek().is_some() {
                        code.push_str(", ");
                    }
                }

                code.push('}');
            }
            Value::Field(operand, name) => {
                self.emit_expr(operand, code);
                code.push_str(&format!(".{}", name));
            }
            Value::TmpVar(t) => {
                if let Some(expr) = t.immediate.get() {
                    self.emit_expr(expr, code);
                } else {
                    code.push_str(&format!("t{}", t.index));
                }
            }
            Value::Var(_, name) => code.push_str(name),
        }
    }
}

/*
fn immediate<'a, 'tcx>(expr: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
    if let ExprKind::Value(Value::TmpVar(t)) = expr.kind() {
        if let Some(expr) = t.immediate.get() {
            return expr;
        }
    }
    expr
}
*/
fn c_type(ty: &Type) -> String {
    match ty {
        Type::Int64 => "int64_t".to_string(),
        Type::Boolean => "bool".to_string(),
        Type::String => "const char *".to_string(),
        Type::NativeInt => "int".to_string(),
        Type::Tuple(_) => {
            let mut buffer = String::new();
            encode_ty(ty, &mut buffer);
            format!("struct _{}", buffer)
        }
    }
}

/// Encode type to C struct type name in universal way. "Universal" here means
/// it is independent of runtime environment and machine architecture.
///
/// ## Integer types
///
/// ```ignore
/// +-----+-------------------------+
/// | "i" | digits (number of bits) |
/// +-----+-------------------------+
/// ```
///
/// ## Tuple type
///
/// ```ignore
/// +-----+---------------------------+----------+
/// | "T" | digits (number of fields) | (fields) |
/// +-----+---------------------------+----------+
/// ```
///
/// ## Other types
///
/// | Type           | Format |
/// | -------------- | ------ |
/// | `boolean`      | `"b"`  |
/// | `string`       | `"s"`  |
/// | `int` (C type) | `"ni"` |
///
fn encode_ty(ty: &Type, buffer: &mut String) {
    match ty {
        Type::Int64 => buffer.push_str("i64"),
        Type::Boolean => buffer.push('b'),
        Type::String => buffer.push('s'),
        Type::NativeInt => buffer.push_str("ni"),
        Type::Tuple(fs) => {
            buffer.push('T');
            buffer.push_str(&fs.len().to_string());
            for fty in fs {
                encode_ty(fty, buffer);
            }
        }
    }
}
