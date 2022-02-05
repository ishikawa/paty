//! C code generator
use super::ir::{
    CallingConvention, Expr, ExprKind, FormatSpec, Function, Parameter, Program, Stmt, TmpVar,
};
use crate::ty::{FunctionSignature, Type};

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

    #[allow(clippy::mutable_key_type)]
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

        // Emit declarations
        for ty in program.decl_types() {
            self.emit_decl_type(ty, &mut code);
        }

        for fun in program.functions() {
            self.emit_function_declaration(fun, &mut code);
        }
        code.push('\n');

        // Emit functions
        for fun in program.functions() {
            self.emit_function(fun, &mut code);
            code.push('\n');
        }

        code
    }

    #[allow(clippy::mutable_key_type)]
    fn emit_decl_type<'t>(&mut self, ty: &'t Type<'tcx>, code: &mut String) {
        // Zero-size data should not has declaration.
        if ty.is_zero_sized() {
            return;
        }

        // Emit C struct.
        // Note that C structure have to contain at least one member.
        match ty {
            Type::Tuple(fs) => {
                code.push_str(&c_type(ty));
                code.push_str(" {\n");

                for (i, fty) in fs.iter().enumerate() {
                    if !fty.is_zero_sized() {
                        code.push_str(&c_type(fty));
                        code.push(' ');
                        code.push_str(&format!("_{};\n", i));
                    }
                }

                code.push_str("};\n\n");
            }
            Type::Struct(struct_ty) => {
                code.push_str(&c_type(ty));
                code.push_str(" {\n");
                for (name, fty) in struct_ty.fields() {
                    if !fty.is_zero_sized() {
                        code.push_str(&c_type(fty));
                        code.push(' ');
                        code.push_str(&format!("{};\n", name));
                    }
                }
                code.push_str("};\n\n");
            }
            Type::Int64 | Type::Boolean | Type::String | Type::NativeInt => {
                // no emit
            }
            Type::Named(named_ty) => {
                unreachable!("untyped code for named type `{}`", named_ty.name())
            }
            Type::Undetermined => unreachable!("untyped code"),
        };
    }

    fn emit_function_declaration(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
        // main function
        if fun.is_entry_point {
            return;
        }

        if fun.retty.is_zero_sized() {
            code.push_str("void");
        } else {
            code.push_str(&c_type(fun.retty));
        }
        code.push(' ');
        let mangled_name = mangle_name(&fun.signature);
        code.push_str(&mangled_name);
        code.push('(');
        for (i, param) in fun.params.iter().enumerate() {
            if param.ty().is_zero_sized() {
                continue;
            }

            code.push_str(&c_type(param.ty()));
            code.push(' ');
            match param {
                Parameter::TmpVar(t) => code.push_str(&tmp_var(t)),
                Parameter::Var(v) => code.push_str(v.name()),
            };

            if i != (fun.params.len() - 1) {
                code.push_str(", ");
            }
        }
        code.push(')');
        code.push(';');
        code.push('\n');
    }

    fn emit_function(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
        if fun.is_entry_point {
            // 'main' must return 'int'
            code.push_str(&c_type(&Type::NativeInt));
        } else if fun.retty.is_zero_sized() {
            code.push_str("void");
        } else {
            code.push_str(&c_type(fun.retty));
        }
        code.push(' ');

        // `main` function is C function
        if fun.is_entry_point {
            code.push_str(&fun.name);
        } else {
            let mangled_name = mangle_name(&fun.signature);
            code.push_str(&mangled_name);
        }

        code.push('(');
        for (i, param) in fun.params.iter().enumerate() {
            if param.ty().is_zero_sized() {
                continue;
            }

            code.push_str(&c_type(param.ty()));
            code.push(' ');
            match param {
                Parameter::TmpVar(t) => code.push_str(&tmp_var(t)),
                Parameter::Var(v) => code.push_str(v.name()),
            };

            if i != (fun.params.len() - 1) {
                code.push_str(", ");
            }
        }
        code.push(')');
        code.push('\n');

        // body
        code.push_str("{\n");
        for param in &fun.params {
            // Emit code to ignore unused variable.
            if let Parameter::TmpVar(t) = param {
                if t.used.get() == 0 {
                    code.push_str(&format!("(void){};\n", tmp_var(t)));
                }
            }
        }

        for stmt in &fun.body {
            self.emit_stmt(stmt, code);
        }
        code.push_str("}\n");
    }

    fn emit_stmt(&mut self, stmt: &Stmt<'a, 'tcx>, code: &mut String) {
        match stmt {
            Stmt::TmpVarDef { var, init, pruned } => {
                if !pruned.get() && !init.ty().is_zero_sized() {
                    // If a temporary variable is not referenced from anywhere,
                    // we don't emit an assignment statement.
                    if var.used.get() > 0 {
                        code.push_str(&c_type(init.ty()));
                        code.push(' ');
                        code.push_str(&tmp_var(var));
                        code.push_str(" = ");
                    }

                    // Emit init statement if needed
                    if var.used.get() > 0 || self.has_side_effect(init) {
                        self.emit_expr(init, code);
                        code.push_str(";\n");
                    }
                }
            }
            Stmt::VarDef { name, init } => {
                if !init.ty().is_zero_sized() {
                    code.push_str(&c_type(init.ty()));
                    code.push(' ');
                    code.push_str(name);
                    code.push_str(" = ");
                    self.emit_expr(init, code);
                    code.push_str(";\n");
                }
            }
            Stmt::Ret(expr) => {
                code.push_str("return");
                if !expr.ty().is_zero_sized() {
                    code.push(' ');
                    self.emit_expr(expr, code);
                }
                code.push_str(";\n");
            }
            Stmt::Phi { var, value, pruned } => {
                if !pruned.get() {
                    if var.used.get() > 0 {
                        code.push_str(&tmp_var(var));
                        code.push_str(" = ");
                    }
                    self.emit_expr(value, code);
                    code.push_str(";\n");
                }
            }
            Stmt::Cond { branches, var } => {
                if var.used.get() > 0 {
                    code.push_str(&c_type(var.ty));
                    code.push(' ');
                    code.push_str(&tmp_var(var));
                    code.push_str(";\n");
                }

                // Construct "if-else" statement from each branches.
                // If a branch has only one branch and it has no condition,
                // this loop finally generate a block statement.
                for (i, branch) in branches.iter().enumerate() {
                    if i > 0 {
                        code.push_str("else ");
                    }

                    if let Some(condition) = branch.condition {
                        code.push_str("if (");
                        self.emit_expr(condition, code);
                        code.push_str(") ");
                    }

                    // body (block)
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
            ExprKind::Call { name, args, cc } => {
                if let CallingConvention::Std(signature) = cc {
                    let mangled_name = mangle_name(signature);
                    code.push_str(&format!("{}(", mangled_name));
                } else {
                    code.push_str(&format!("{}(", name));
                }

                for (i, arg) in args.iter().enumerate() {
                    self.emit_expr(arg, code);

                    if i != (args.len() - 1) {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            ExprKind::Printf(specs) => {
                // emit printf() and format specifiers

                code.push_str("printf(\"");
                for spec in specs {
                    match spec {
                        FormatSpec::Str(s) => {
                            for c in s.escape_default() {
                                code.push(c);
                            }
                        }
                        FormatSpec::Value(value) => {
                            match value.ty() {
                                Type::Int64 => {
                                    // Use standard conversion specifier macros for integer types.
                                    code.push_str("%\" PRId64 \"");
                                }
                                Type::Boolean => {
                                    // "true" / "false"
                                    code.push_str("%s");
                                }
                                Type::String => {
                                    code.push_str("%s");
                                }
                                Type::NativeInt => {
                                    code.push_str("%d");
                                }
                                Type::Tuple(_) | Type::Struct(_) => {
                                    unreachable!("compound value can't be printed: {:?}", value);
                                }
                                Type::Named(name) => {
                                    unreachable!("untyped for the type named: {}", name)
                                }
                                Type::Undetermined => unreachable!("untyped code"),
                            }
                        }
                    }
                }
                code.push('"');

                // arguments
                let mut is_first_arg = true;
                let mut it = specs
                    .iter()
                    .filter(|spec| matches!(spec, FormatSpec::Value(_)))
                    .peekable();

                while let Some(spec) = it.next() {
                    if let FormatSpec::Value(value) = spec {
                        if is_first_arg {
                            code.push_str(", ");
                            is_first_arg = false;
                        }

                        match value.ty() {
                            Type::Int64 | Type::String | Type::NativeInt => {
                                self.emit_expr(value, code);
                            }
                            Type::Boolean => {
                                match immediate(value).kind() {
                                    ExprKind::Bool(true) => code.push_str("\"true\""),
                                    ExprKind::Bool(false) => code.push_str("\"false\""),
                                    _ => {
                                        // "true" / "false"
                                        code.push('(');
                                        self.emit_expr(value, code);
                                        code.push_str(" ? \"true\" : \"false\"");
                                        code.push(')');
                                    }
                                }
                            }
                            Type::Tuple(_) | Type::Struct(_) => {
                                unreachable!("compound value can't be printed: {:?}", value);
                            }
                            Type::Named(name) => {
                                unreachable!("untyped for the type named: {}", name)
                            }
                            Type::Undetermined => unreachable!("untyped code"),
                        }
                    }

                    if it.peek().is_some() {
                        code.push_str(", ");
                    }
                }
                code.push(')');
            }
            ExprKind::Int64(n) => {
                match expr.ty() {
                    Type::Int64 => {
                        // Use standard macros for integer constant expression to expand
                        // a value to the type int_least_N.
                        code.push_str(&format!("INT64_C({})", *n))
                    }
                    Type::NativeInt => code.push_str(&format!("{}", *n)),
                    _ => unreachable!("Unexpected integral type: {}", expr.ty()),
                }
            }
            ExprKind::Bool(b) => {
                // Use standard macros for boolean constant expression.
                if *b {
                    code.push_str("true");
                } else {
                    code.push_str("false");
                }
            }
            ExprKind::Str(s) => {
                code.push_str("u8\"");
                for c in s.escape_default() {
                    code.push(c);
                }
                code.push('"');
            }
            ExprKind::Tuple(values) => {
                // Specify struct type explicitly.
                code.push('(');
                code.push_str(&c_type(expr.ty()));
                code.push(')');

                // Initialize tuple struct with designated initializers.
                code.push('{');

                let mut peekable = values.iter().enumerate().peekable();

                while let Some((i, value)) = peekable.next() {
                    if value.ty().is_zero_sized() {
                        continue;
                    }

                    code.push_str(&format!("._{} = ", i));
                    self.emit_expr(value, code);

                    if peekable.peek().is_some() {
                        code.push_str(", ");
                    }
                }

                code.push('}');
            }
            ExprKind::StructValue(_, fs) => {
                // Specify struct type explicitly.
                code.push('(');
                code.push_str(&c_type(expr.ty()));
                code.push(')');

                // Initialize tuple struct with designated initializers.
                code.push('{');

                let mut peekable = fs.iter().peekable();

                while let Some((name, value)) = peekable.next() {
                    if value.ty().is_zero_sized() {
                        continue;
                    }

                    code.push_str(&format!(".{} = ", name));
                    self.emit_expr(value, code);

                    if peekable.peek().is_some() {
                        code.push_str(", ");
                    }
                }

                code.push('}');
            }
            ExprKind::IndexAccess { operand, index } => {
                self.emit_expr(operand, code);
                code.push_str(&format!("._{}", index));
            }
            ExprKind::FieldAccess { operand, name } => {
                self.emit_expr(operand, code);
                code.push_str(&format!(".{}", name));
            }
            ExprKind::TmpVar(t) => {
                if let Some(expr) = t.immediate.get() {
                    self.emit_expr(expr, code);
                } else {
                    code.push_str(&tmp_var(t));
                }
            }
            ExprKind::Var(var) => code.push_str(var.name()),
        }
    }

    fn has_side_effect(&self, expr: &Expr) -> bool {
        match expr.kind() {
            ExprKind::Minus(a) | ExprKind::Not(a) => self.has_side_effect(a),
            ExprKind::Add(a, b)
            | ExprKind::Sub(a, b)
            | ExprKind::Mul(a, b)
            | ExprKind::Div(a, b)
            | ExprKind::Eq(a, b)
            | ExprKind::Ne(a, b)
            | ExprKind::Lt(a, b)
            | ExprKind::Le(a, b)
            | ExprKind::Gt(a, b)
            | ExprKind::Ge(a, b)
            | ExprKind::And(a, b)
            | ExprKind::Or(a, b) => self.has_side_effect(a) || self.has_side_effect(b),
            ExprKind::Call { .. } => true,
            ExprKind::Printf(_) => true,
            ExprKind::Tuple(fs) => fs.iter().any(|sub_expr| self.has_side_effect(sub_expr)),
            ExprKind::StructValue(_, fs) => fs
                .iter()
                .any(|(_, sub_expr)| self.has_side_effect(sub_expr)),
            ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::IndexAccess { .. }
            | ExprKind::FieldAccess { .. }
            | ExprKind::TmpVar(_)
            | ExprKind::Var(_) => false,
        }
    }
}

fn immediate<'a, 'tcx>(expr: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
    if let ExprKind::TmpVar(t) = expr.kind() {
        if let Some(expr) = t.immediate.get() {
            return expr;
        }
    }
    expr
}

fn tmp_var(t: &TmpVar) -> String {
    format!("t{}", t.index)
}

fn c_type(ty: &Type) -> String {
    match ty {
        Type::Int64 => "int64_t".to_string(),
        Type::Boolean => "bool".to_string(),
        Type::String => "const char *".to_string(),
        Type::NativeInt => "int".to_string(),
        Type::Tuple(_) | Type::Struct(_) => {
            let mut buffer = String::new();
            encode_ty(ty, &mut buffer);
            format!("struct _{}", buffer)
        }
        Type::Named(named_ty) => c_type(named_ty.expect_ty()),
        Type::Undetermined => unreachable!("untyped code"),
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
/// ## Struct type
///
/// ```ignore
/// +-----+-------+
/// | "S" | name  |
/// +-----+-------+
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
        Type::Struct(struct_ty) => {
            buffer.push('S');
            buffer.push_str(struct_ty.name());
        }
        Type::Named(named_ty) => {
            encode_ty(named_ty.expect_ty(), buffer);
        }
        Type::Undetermined => unreachable!("untyped code"),
    }
}

/// Function name mangling scheme
///
/// +------+-------------------------------------------+------+-----------------------------+-------------+
/// | "_Z" | digits (The length of the following name) | name | digits (The number of args) | (arg types) |
/// +------+-------------------------------------------+------+-----------------------------+-------------+
///
fn mangle_name(signature: &FunctionSignature<'_>) -> String {
    let mut name = format!(
        "_Z{}{}{}",
        signature.name().len(),
        signature.name(),
        signature.params().len()
    );

    for p in signature.params() {
        encode_ty(p.bottom_ty(), &mut name);
    }

    name
}
