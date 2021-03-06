//! C code generator
use crate::ir::inst::{
    CallingConvention, Expr, ExprKind, FormatSpec, Function, Parameter, Program, Stmt, TmpVar,
};
use crate::ty::{expand_union_ty_array, FunctionSignature, Type};
use std::collections::HashSet;

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

        // --- Emit declarations
        // Some types are represented as the same structure in the C language,
        // so once a type is output, it should not be output twice.
        let mut emitted_c_types = HashSet::new();

        for ty in program.decl_types() {
            self.emit_decl_type(ty, &mut emitted_c_types, &mut code);
        }

        for fun in program.functions() {
            if !fun.is_entry_point {
                self.emit_function_declaration(fun, &mut code);
                code.push(';');
                code.push('\n');
            }
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
    fn emit_decl_type<'t>(
        &mut self,
        ty: &'t Type<'tcx>,
        emitted_c_types: &mut HashSet<String>,
        code: &mut String,
    ) {
        // Zero-size data should not has declaration.
        if ty.is_zero_sized() {
            return;
        }

        // Emit C struct.
        // Note that C structure have to contain at least one member.
        let c_type_str = c_type(ty);

        if emitted_c_types.contains(&c_type_str) {
            return;
        }

        match ty {
            Type::Tuple(fs) => {
                code.push_str(&c_type_str);
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
                code.push_str(&c_type_str);
                code.push_str(" {\n");
                for f in struct_ty.fields() {
                    if !f.ty().is_zero_sized() {
                        code.push_str(&c_type(f.ty()));
                        code.push(' ');
                        code.push_str(&format!("{};\n", f.name()));
                    }
                }
                code.push_str("};\n\n");
            }
            Type::Union(member_types) => {
                let member_types = expand_union_ty_array(member_types);
                code.push_str(&c_type_str);
                code.push_str(" {\n");

                // tag filed
                code.push_str(&c_type(&Type::Int64));
                code.push(' ');
                code.push_str("tag;\n");

                // union
                code.push_str("union {\n");
                for (tag, mty) in member_types.iter().enumerate() {
                    code.push_str(&c_type(mty));
                    code.push(' ');
                    code.push_str(&format!("_{};\n", tag));
                }
                code.push_str("} u;\n");

                code.push_str("};\n\n");
            }
            Type::Int64
            | Type::Boolean
            | Type::String
            | Type::NativeInt
            | Type::LiteralInt64(_)
            | Type::LiteralBoolean(_)
            | Type::LiteralString(_) => {
                // no emit
                return;
            }
            Type::Named(named_ty) => {
                unreachable!("untyped code for named type `{}`", named_ty.name())
            }
            Type::Undetermined => unreachable!("untyped code"),
        };

        emitted_c_types.insert(c_type_str);
    }

    fn emit_function_declaration(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
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
    }

    fn emit_function(&mut self, fun: &Function<'a, 'tcx>, code: &mut String) {
        self.emit_function_declaration(fun, code);
        code.push('\n');

        // body
        code.push_str("{\n");
        for param in &fun.params {
            if !param.ty().is_zero_sized() {
                // Emit code to ignore unused variable.
                if let Parameter::TmpVar(t) = param {
                    if t.used() == 0 {
                        code.push_str(&format!("(void){};\n", tmp_var(t)));
                    }
                }
                // TODO: Don't emit `(void)...` unless it is needed.
                else if let Parameter::Var(var) = param {
                    code.push_str(&format!("(void){};\n", var.name()));
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
            Stmt::TmpVarDef(def) => {
                if !def.init().ty().is_zero_sized() {
                    // If a temporary variable is not referenced from anywhere,
                    // we don't emit an assignment statement.
                    if def.var().used() > 0 {
                        code.push_str(&c_type(def.init().ty()));
                        code.push(' ');
                        code.push_str(&tmp_var(def.var()));
                        code.push_str(" = ");
                    }

                    // Emit init statement
                    self.emit_expr(def.init(), code);
                    code.push_str(";\n");
                }
            }
            Stmt::VarDef(def) => {
                if !def.init().ty().is_zero_sized() {
                    code.push_str(&c_type(def.init().ty()));
                    code.push(' ');
                    code.push_str(def.name());
                    code.push_str(" = ");
                    self.emit_expr(def.init(), code);
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
            Stmt::Phi(phi) => {
                if phi.var().used() > 0 {
                    code.push_str(&tmp_var(phi.var()));
                    code.push_str(" = ");
                }
                self.emit_expr(phi.value(), code);
                code.push_str(";\n");
            }
            Stmt::Cond(cond) => {
                if cond.var.used() > 0 {
                    code.push_str(&c_type(cond.var.ty()));
                    code.push(' ');
                    code.push_str(&tmp_var(cond.var));

                    // Initialize with zero value.
                    code.push_str(" = ");
                    code.push_str(zero_value(cond.var.ty()));

                    code.push_str(";\n");
                }

                // Construct "if-else" statement from each branches.
                // If a branch has only one branch and it has no condition,
                // this loop finally generate a block statement.
                for (i, branch) in cond.branches.iter().enumerate() {
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
                code.push('(');
                self.emit_expr(operand, code);
                code.push(')');
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
            ExprKind::CondAndAssign { cond, var } => {
                code.push('(');
                // TODO: Optimization: replace CondAndAssign with Expr if used == 0
                if var.used() == 0 {
                    if let Some(cond) = cond {
                        self.emit_expr(cond, code);
                    } else {
                        code.push_str("true");
                    }
                } else {
                    if let Some(cond) = cond {
                        self.emit_expr(cond, code);
                        code.push_str(" && ");
                    }
                    code.push('(');
                    code.push_str(&tmp_var(var));
                    code.push_str(" = true");
                    code.push(')');
                }
                code.push(')');
            }
            ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => {
                code.push('(');
                code.push('(');
                self.emit_expr(cond, code);
                code.push(')');
                code.push_str(" ? ");
                self.emit_expr(then_value, code);
                code.push_str(" : ");
                self.emit_expr(else_value, code);
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
                            code.push_str(&escape_c_string(s));
                        }
                        FormatSpec::Value(value) => {
                            match value.ty() {
                                Type::Int64 | Type::LiteralInt64(_) => {
                                    // Use standard conversion specifier macros for integer types.
                                    code.push_str("%\" PRId64 \"");
                                }
                                Type::Boolean | Type::LiteralBoolean(_) => {
                                    // "true" / "false"
                                    code.push_str("%s");
                                }
                                Type::String | Type::LiteralString(_) => {
                                    code.push_str("%s");
                                }
                                Type::NativeInt => {
                                    code.push_str("%d");
                                }
                                Type::Tuple(_) | Type::Struct(_) | Type::Union(_) => {
                                    unreachable!("compound value can't be printed: {:?}", value);
                                }
                                Type::Named(_) | Type::Undetermined => {
                                    unreachable!("unexpected type: {:?}", value)
                                }
                            }
                        }
                        FormatSpec::Quoted(value) => match value.ty() {
                            Type::String | Type::LiteralString(_) => {
                                code.push_str("\\\"%s\\\"");
                            }
                            _ => unreachable!("quoted value must be a string: {:?}", value),
                        },
                    }
                }
                code.push('"');

                // arguments
                for spec in specs {
                    let value = match spec {
                        FormatSpec::Value(value) => value,
                        FormatSpec::Quoted(value) => value,
                        FormatSpec::Str(_) => continue,
                    };

                    code.push_str(", ");

                    match value.ty() {
                        Type::Int64
                        | Type::String
                        | Type::NativeInt
                        | Type::LiteralInt64(_)
                        | Type::LiteralString(_) => {
                            self.emit_expr(value, code);
                        }
                        Type::Boolean | Type::LiteralBoolean(_) => {
                            match value.kind() {
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
                        Type::Tuple(_) | Type::Struct(_) | Type::Union(_) => {
                            unreachable!("compound value can't be printed: {:?}", value);
                        }
                        Type::Named(name) => {
                            unreachable!("untyped for the type named: {}", name)
                        }
                        Type::Undetermined => unreachable!("untyped code"),
                    }
                }
                code.push(')');
            }
            &ExprKind::Int64(n) => {
                // We have to use INT_MIN macro to represent the minimum value of
                // 64 bit integers.
                //
                // There is no such thing as negative literal in C/C++: just the unary
                // negative operator with a positive integer which produces a compile time
                // evaluated constant.
                //
                // `9223372036854775808` is too big to fit into a 64 bit signed integral type,
                // so the behavior of negating this and assigning to a signed 64 bit integral
                // type is implementation defined.
                match n {
                    // prints INT_XXX macro directory
                    i64::MIN => code.push_str("INT64_MIN"),
                    i64::MAX => code.push_str("INT64_MAX"),
                    _ => {
                        match expr.ty() {
                            Type::Int64 | Type::LiteralInt64(_) => {
                                // Use standard macros for integer constant expression to expand
                                // a value to the type int_least_N.
                                code.push_str(&format!("INT64_C({})", n))
                            }
                            Type::NativeInt => code.push_str(&n.to_string()),
                            _ => unreachable!("Unexpected integral type: {}", expr.ty()),
                        }
                    }
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
                code.push_str(&format!("u8\"{}\"", escape_c_string(s)));
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
            ExprKind::StructValue(fs) => {
                // Specify struct type explicitly.
                code.push('(');
                code.push_str(&c_type(expr.ty()));
                code.push(')');

                // Initialize struct with designated initializers.
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
            ExprKind::UnionTag(operand) => {
                self.emit_expr(operand, code);
                code.push_str(".tag");
            }
            ExprKind::UnionMemberAccess { operand, tag } => {
                self.emit_expr(operand, code);
                code.push_str(&format!(".u._{}", tag));
            }
            ExprKind::UnionValue { value, tag } => {
                // Specify struct type explicitly.
                code.push('(');
                code.push_str(&c_type(expr.ty()));
                code.push(')');

                // Initialize tagged union struct with designated initializers.
                code.push('{');
                code.push_str(&format!(".tag = {}, ", tag));
                code.push_str(".u = {");
                code.push_str(&format!("._{} = ", tag));
                self.emit_expr(value, code);
                code.push('}');
                code.push('}');
            }
            ExprKind::TmpVar(t) => {
                code.push_str(&tmp_var(t));
            }
            ExprKind::Var(var) => code.push_str(var.name()),
        }
    }
}

fn tmp_var(t: &TmpVar) -> String {
    format!("_t{}", t.index())
}

fn c_type(ty: &Type) -> String {
    match ty {
        Type::Int64 | Type::LiteralInt64(_) => "int64_t".to_string(),
        Type::Boolean | Type::LiteralBoolean(_) => "bool".to_string(),
        Type::String | Type::LiteralString(_) => "const char *".to_string(),
        Type::NativeInt => "int".to_string(),
        Type::Tuple(_) | Type::Struct(_) | Type::Union(_) => {
            let mut buffer = String::new();
            encode_ty(ty, &mut buffer);
            format!("struct _{}", buffer)
        }
        Type::Named(named_ty) => c_type(named_ty.expect_ty()),
        Type::Undetermined => unreachable!("untyped code"),
    }
}

// Anything in C can be initialized with = 0; this initializes
// numeric elements to zero and pointers null.
fn zero_value(ty: &Type) -> &'static str {
    match ty {
        Type::Int64
        | Type::Boolean
        | Type::String
        | Type::NativeInt
        | Type::LiteralInt64(_)
        | Type::LiteralBoolean(_)
        | Type::LiteralString(_) => "0",
        Type::Tuple(_) | Type::Struct(_) | Type::Union(_) => "{0}",
        Type::Named(named_ty) => zero_value(named_ty.expect_ty()),
        Type::Undetermined => unreachable!("untyped code"),
    }
}

/// Returns a new string from the input to produce literal that are legal in
/// C11's `u8` string.
fn escape_c_string(value: &str) -> String {
    let mut escaped = String::new();

    for c in value.chars() {
        match c {
            '\t' => escaped.push_str("\\t"),
            '\r' => escaped.push_str("\\r"),
            '\n' => escaped.push_str("\\n"),
            '\'' => escaped.push_str("\\'"),
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            _ => escaped.push(c),
        };
    }

    escaped
}

/// Encode type to C struct type name in universal way. "Universal" here means
/// it is independent of runtime environment and machine architecture.
///
/// Types that are represented as the same structure in the C language must
/// return the same string.
///
/// ## 64 bits Integer type
///
/// ```ignore
/// +-----+
/// | "n" |
/// +-----+
/// ```
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
/// +-----+---------------------------+---------------+
/// | "T" | digits (number of fields) | (field types) |
/// +-----+---------------------------+---------------+
/// ```
///
/// ## Anonymous struct type
///
/// ```ignore
/// +-----+---------------------------+----------------+
/// | "S" | digits (number of fields) | (named fields) |
/// +-----+---------------------------+----------------+
///
/// named field:
/// +------+-------------------------------------------+------+
/// | type | digits (The length of the following name) | name |
/// +------+-------------------------------------------+------+
///
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
/// ## Union type
///
/// ```ignore
/// +-----+---------------------------+---------------+
/// | "U" | digits (number of fields) | (field types) |
/// +-----+---------------------------+---------------+
/// ```
///
/// ## Other types (including literal types)
///
/// NOTE: We don't care a type is literal type or not to make it compatible in
/// C struct type.
///
/// | Type           | Format |
/// | -------------- | ------ |
/// | `boolean`      | `"b"`  |
/// | `string`       | `"s"`  |
/// | `int` (C type) | `"ni"` |
///
fn encode_ty(ty: &Type, buffer: &mut String) {
    match ty {
        Type::Int64 | Type::LiteralInt64(_) => buffer.push('n'),
        Type::Boolean | Type::LiteralBoolean(_) => buffer.push('b'),
        Type::String | Type::LiteralString(_) => buffer.push('s'),
        Type::NativeInt => buffer.push_str("ni"),
        Type::Tuple(fs) => {
            buffer.push('T');
            buffer.push_str(&fs.len().to_string());
            for fty in fs {
                encode_ty(fty, buffer);
            }
        }
        Type::Union(member_types) => {
            let member_types = expand_union_ty_array(member_types);

            buffer.push('U');
            buffer.push_str(&member_types.len().to_string());
            for mty in member_types {
                encode_ty(mty, buffer);
            }
        }
        Type::Struct(struct_ty) => {
            buffer.push('S');
            if let Some(name) = struct_ty.name() {
                buffer.push_str(name);
            } else {
                buffer.push_str(&struct_ty.fields().len().to_string());
                for f in struct_ty.fields() {
                    encode_ty(f.ty(), buffer);
                    buffer.push_str(&f.name().len().to_string());
                    buffer.push_str(f.name());
                }
            }
        }
        Type::Named(named_ty) => {
            encode_ty(named_ty.expect_ty(), buffer);
        }
        Type::Undetermined => unreachable!("untyped code"),
    }
}

/// Function name mangling scheme.
///
/// Types that are treated as different types in this programming language must
/// return separate strings.
///
/// +------+-------------------------------------------+------+-----------------------------+-------------+
/// | "_Z" | digits (The length of the following name) | name | digits (The number of args) | (arg types) |
/// +------+-------------------------------------------+------+-----------------------------+-------------+
///
/// ## Literal types
///
/// To make function overloading work properly, we have to encode literal types.
///
/// ### integers
///
/// +-----+-----+-------------------------+-----+---------+
/// | "L" | "i" | digits (number of bits) | "_" | integer |
/// +-----+-----+-------------------------+-----+---------+
///
/// ### boolean
///
/// +-----+-----+-----------------------+
/// | "L" | "b" | "0": false, "1": true |
/// +-----+-----+-----------------------+
///
/// ### string
///
/// +-----+-----+------------------------------------+-----+-----------------------------------+
/// | "L" | "s" | digits (The length of "b58" field) | "_" | b58 (base58 encoded string value) |
/// +-----+-----+------------------------------------+-----+-----------------------------------+
///
fn mangle_name(signature: &FunctionSignature<'_>) -> String {
    let mut buffer = format!(
        "_Z{}{}{}",
        signature.name().len(),
        signature.name(),
        signature.params().len()
    );

    for p in signature.params() {
        let pty = p.bottom_ty();

        match pty {
            Type::LiteralInt64(n) => {
                buffer.push('L');
                buffer.push('i');
                buffer.push_str("64");
                buffer.push('_');
                buffer.push_str(&n.to_string());
            }
            Type::LiteralBoolean(b) => {
                buffer.push('L');
                buffer.push('b');
                if *b {
                    buffer.push('1');
                } else {
                    buffer.push('0');
                }
            }
            Type::LiteralString(s) => {
                let encoded = bs58::encode(s).into_string();

                buffer.push('L');
                buffer.push('s');

                // Encode literal string with base58 encoding
                buffer.push_str(&encoded.len().to_string());
                buffer.push('_');
                buffer.push_str(&encoded);
            }
            // fall back to encode_ty()
            _ => encode_ty(pty, &mut buffer),
        }
    }

    buffer
}
