//! Semantic analysis
use self::error::{FormatSymbols, SemanticError, SemanticErrorKind};
use crate::syntax::{PatternKind, StmtKind, Typable};
use crate::ty::{StructTy, TypedField};
use crate::{
    syntax,
    ty::{Type, TypeContext},
};
use std::collections::{HashMap, HashSet};

mod error;
mod usefulness;

#[derive(Debug)]
struct Binding<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> Binding<'tcx> {
    pub fn new(name: String, ty: &'tcx Type<'tcx>) -> Self {
        Self { name, ty }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

#[derive(Debug, Default)]
struct Scope<'a, 'tcx> {
    parent: Option<&'a Scope<'a, 'tcx>>,
    bindings: HashMap<String, Binding<'tcx>>,
}

impl<'a, 'tcx> Scope<'a, 'tcx> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn from_parent(parent: &'a Scope<'a, 'tcx>) -> Self {
        Self {
            parent: Some(parent),
            bindings: HashMap::new(),
        }
    }

    pub fn insert(&mut self, binding: Binding<'tcx>) {
        self.bindings.insert(binding.name().to_string(), binding);
    }

    pub fn get(&self, name: &str) -> Option<&Binding<'tcx>> {
        if let Some(binding) = self.bindings.get(name) {
            Some(binding)
        } else if let Some(parent) = self.parent {
            parent.get(name)
        } else {
            None
        }
    }

    /// Returns an iterator which iterates bindings in this scope.
    pub fn bindings_iter(&self) -> impl Iterator<Item = (&str, &Binding<'tcx>)> {
        self.bindings.iter().map(|(k, v)| (k.as_str(), v))
    }
}

#[derive(Debug)]
struct Errors<'tcx> {
    errors: Vec<SemanticError<'tcx>>,
}

impl<'tcx> Errors<'tcx> {
    pub fn new() -> Self {
        Self {
            errors: Vec::with_capacity(0),
        }
    }

    pub fn to_vec(&self) -> Vec<SemanticError<'tcx>> {
        self.errors.clone()
    }

    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }

    pub fn push<S: ToString>(&mut self, kind: SemanticErrorKind<'tcx>, source: S) {
        self.errors
            .push(SemanticError::new(kind, source.to_string()));
    }

    pub fn extend(&mut self, err: Vec<SemanticError<'tcx>>) {
        self.errors.extend(err);
    }
}

// Analyze an AST and returns error if any.
#[allow(clippy::map_entry)]
pub fn analyze<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    body: &[syntax::TopLevel<'nd, 'tcx>],
) -> Result<(), Vec<SemanticError<'tcx>>> {
    let mut errors = Errors::new();
    let mut scope = Scope::new();
    let mut named_types = HashMap::new();
    let mut functions: Vec<&syntax::Function<'nd, 'tcx>> = vec![];

    // 1. Collect named types before analyze program.
    for top_level in body {
        if let syntax::TopLevel::Declaration(decl) = top_level {
            let (name, ty) = match decl.kind() {
                syntax::DeclarationKind::Struct(struct_decl) => {
                    (struct_decl.name().to_string(), struct_decl.ty())
                }
                syntax::DeclarationKind::TypeAlias(alias) => (alias.name().to_string(), alias.ty()),
                syntax::DeclarationKind::Function(_) => {
                    continue;
                }
            };

            if named_types.contains_key(&name) {
                errors.push(SemanticErrorKind::DuplicateNamedType { name }, top_level);
            } else {
                named_types.insert(name, ty);
            }
        }
    }

    // 2. For all explicit type annotation/declaration(s), resolve these types.
    for top_level in body {
        analyze_explicit_type_annotations_top_level(tcx, top_level, &named_types, &mut errors);
    }

    // 3. For all function declarations, collect declarations.
    for top_level in body {
        if let syntax::TopLevel::Declaration(decl) = top_level {
            if let syntax::DeclarationKind::Function(fun) = decl.kind() {
                let sig = fun.signature();

                if functions.iter().any(|f| f.signature() == sig) {
                    errors.push(SemanticErrorKind::DuplicateFunction { signature: sig }, fun);
                } else {
                    functions.push(fun);
                }
            }
        }
    }

    // 4. Analyze declarations and statements
    for top_level in body {
        match top_level {
            syntax::TopLevel::Declaration(decl) => {
                analyze_decl(
                    tcx,
                    decl,
                    &mut scope,
                    &mut functions,
                    &mut named_types,
                    &mut errors,
                );
            }
            syntax::TopLevel::Stmt(stmt) => {
                analyze_stmt(
                    tcx,
                    stmt,
                    &mut scope,
                    &functions,
                    &mut named_types,
                    &mut errors,
                );
            }
        }
    }

    // 5. Every function's return type is inferred. Iterates call sites and
    //    assign expression type if not assigned.
    if errors.is_empty() {
        for top_level in body {
            match top_level {
                syntax::TopLevel::Declaration(decl) => {
                    if let syntax::DeclarationKind::Function(fun) = decl.kind() {
                        for stmt in fun.body() {
                            analyze_call_sites_stmt(tcx, stmt, &functions);
                        }
                    }
                }
                syntax::TopLevel::Stmt(stmt) => {
                    analyze_call_sites_stmt(tcx, stmt, &functions);
                }
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors.to_vec())
    }
}

#[allow(clippy::needless_bool)]
fn unify_type<'tcx, T: Typable<'tcx> + std::fmt::Debug + ToString>(
    expected: &'tcx Type<'tcx>,
    node: &T,
    errors: &mut Errors<'tcx>,
) -> bool {
    if let Some(actual) = node.ty() {
        if !expect_assignable_type(expected, actual, node, errors) {
            //dbg!(expected);
            //dbg!(node);
            false
        } else {
            true
        }
    } else {
        node.assign_ty(expected);
        true
    }
}

fn expect_assignable_type<'tcx>(
    expected: &'tcx Type<'tcx>,
    actual: &'tcx Type<'tcx>,
    source: impl ToString,
    errors: &mut Errors<'tcx>,
) -> bool {
    if !actual.is_assignable_to(expected) {
        errors.push(
            SemanticErrorKind::MismatchedType { expected, actual },
            source,
        );
        false
    } else {
        true
    }
}

fn resolve_type<'tcx>(
    ty: &'tcx Type<'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) -> bool {
    match ty {
        Type::Tuple(fs) => fs.iter().all(|fty| resolve_type(fty, named_types, errors)),
        Type::Union(ms) => ms.iter().all(|mty| resolve_type(mty, named_types, errors)),
        Type::Struct(struct_ty) => struct_ty
            .fields()
            .iter()
            .all(|f| resolve_type(f.ty(), named_types, errors)),
        Type::Named(named_ty) => {
            if named_ty.ty().is_none() {
                if let Some(ty) = named_types.get(named_ty.name()) {
                    named_ty.assign_ty(ty);
                } else {
                    errors.push(
                        SemanticErrorKind::UndefinedNamedType {
                            name: named_ty.name().to_string(),
                        },
                        "",
                    );
                    return false;
                }
            }
            true
        }
        Type::Int64
        | Type::Boolean
        | Type::String
        | Type::Undetermined
        | Type::NativeInt
        | Type::LiteralInt64(_)
        | Type::LiteralBoolean(_)
        | Type::LiteralString(_) => true,
    }
}

//  For all explicit type annotation/declaration(s), resolve these types.
fn analyze_explicit_type_annotations_top_level<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    top_level: &syntax::TopLevel<'nd, 'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match top_level {
        syntax::TopLevel::Declaration(decl) => {
            analyze_explicit_type_annotations_decl(tcx, decl, named_types, errors)
        }
        syntax::TopLevel::Stmt(stmt) => {
            analyze_explicit_type_annotations_stmt(tcx, stmt, named_types, errors)
        }
    }
}
fn analyze_explicit_type_annotations_decl<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    decl: &syntax::Declaration<'nd, 'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match decl.kind() {
        syntax::DeclarationKind::Function(fun) => {
            // Resolved parameter types before using it as key.
            for p in fun.params() {
                resolve_type(p.ty(), named_types, errors);
            }
            for stmt in fun.body() {
                analyze_explicit_type_annotations_stmt(tcx, stmt, named_types, errors);
            }
        }
        syntax::DeclarationKind::Struct(struct_decl) => {
            resolve_type(struct_decl.ty(), named_types, errors);
        }
        syntax::DeclarationKind::TypeAlias(alias) => {
            resolve_type(alias.ty(), named_types, errors);
        }
    }
}
fn analyze_explicit_type_annotations_stmt<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    stmt: &syntax::Stmt<'nd, 'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match stmt.kind() {
        StmtKind::Let { pattern, .. } => {
            if let Some(ty) = pattern.ty() {
                resolve_type(ty, named_types, errors);
            }
        }
        StmtKind::Expr(expr) => {
            analyze_explicit_type_annotations_expr(tcx, expr, named_types, errors)
        }
    }
}
fn analyze_explicit_type_annotations_expr<'nd, 'tcx>(
    _tcx: TypeContext<'tcx>,
    expr: &syntax::Expr<'nd, 'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    if let syntax::ExprKind::Case { arms, .. } = expr.kind() {
        for arm in arms {
            if let Some(ty) = arm.pattern().ty() {
                resolve_type(ty, named_types, errors);
            }
        }
    }
}

fn analyze_decl<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    decl: &syntax::Declaration<'nd, 'tcx>,
    _vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&syntax::Function<'nd, 'tcx>>,
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    if let syntax::DeclarationKind::Function(fun) = decl.kind() {
        // Function definition creates a new scope without a parent scope.
        let mut scope = Scope::new();

        for param in fun.params() {
            //resolve_type(tcx, param.ty(), named_types, errors);
            analyze_let_pattern(
                tcx,
                param.pattern(),
                param.ty(),
                &mut scope,
                functions,
                named_types,
                errors,
            );
        }

        for stmt in fun.body() {
            analyze_stmt(tcx, stmt, &mut scope, functions, named_types, errors);
        }

        // --- return type inference
        let inferred_retty = if let Some(stmt) = fun.body().last() {
            if let StmtKind::Expr(e) = stmt.kind() {
                e.ty()
            } else {
                // Couldn't infer the return type. It should be specified by the return
                // type annotation.
                None
            }
        } else {
            // Empty body function's return type should be unit type.
            Some(tcx.unit())
        };

        match (inferred_retty, fun.retty()) {
            (Some(inferred_retty), Some(retty)) => {
                if !inferred_retty.is_assignable_to(retty) {
                    errors.push(
                        SemanticErrorKind::MismatchedReturnType {
                            signature: fun.signature(),
                            expected: retty,
                            actual: inferred_retty,
                        },
                        fun,
                    );
                }
            }
            (Some(inferred_retty), None) => {
                fun.assign_retty(inferred_retty);
            }
            (None, Some(_retty)) => {
                // The return type is already defined.
            }
            (None, None) => {
                // The return type of function cannot be inferred.
                errors.push(
                    SemanticErrorKind::UnrecognizedReturnType {
                        signature: fun.signature(),
                    },
                    fun,
                );
            }
        };
    }
}
fn analyze_stmts<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    stmts: &[syntax::Stmt<'nd, 'tcx>],
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) -> &'tcx Type<'tcx> {
    // unit type for empty body
    let mut last_stmt_ty = if stmts.is_empty() {
        tcx.unit()
    } else {
        tcx.undetermined()
    };

    for stmt in stmts {
        analyze_stmt(tcx, stmt, vars, functions, named_types, errors);
        if let syntax::StmtKind::Expr(expr) = stmt.kind() {
            if let Some(ty) = expr.ty() {
                last_stmt_ty = ty;
            }
        }
    }
    last_stmt_ty
}
fn analyze_stmt<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    stmt: &syntax::Stmt<'nd, 'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match stmt.kind() {
        &syntax::StmtKind::Let { pattern, rhs } => {
            analyze_expr(tcx, rhs, vars, functions, named_types, errors);
            if !errors.is_empty() {
                return;
            }

            if let Some(pattern_ty) = pattern.ty() {
                // the pattern has an explicit type annotation.
                analyze_let_pattern(
                    tcx,
                    pattern,
                    pattern_ty,
                    vars,
                    functions,
                    named_types,
                    errors,
                );
                unify_type(pattern_ty, rhs, errors);
            } else {
                // otherwise, pattern should be unified with rhs's type.
                analyze_let_pattern(
                    tcx,
                    pattern,
                    rhs.expect_ty(),
                    vars,
                    functions,
                    named_types,
                    errors,
                );
            }
        }
        syntax::StmtKind::Expr(expr) => {
            analyze_expr(tcx, expr, vars, functions, named_types, errors);
        }
    }
}
fn analyze_expr<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &syntax::Expr<'nd, 'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match expr.kind() {
        syntax::ExprKind::Integer(n) => {
            unify_type(tcx.literal_int64(*n), expr, errors);
        }
        syntax::ExprKind::Boolean(b) => {
            unify_type(tcx.literal_boolean(*b), expr, errors);
        }
        syntax::ExprKind::String(s) => {
            unify_type(tcx.literal_string(s.clone()), expr, errors);
        }
        syntax::ExprKind::Tuple(values) => {
            let mut value_types = vec![];

            for value in values {
                analyze_expr(tcx, value, vars, functions, named_types, errors);
                value_types.push(value.ty().unwrap());
            }

            unify_type(tcx.tuple(value_types), expr, errors);
        }
        syntax::ExprKind::Struct(struct_value) => {
            if let Some(struct_name) = struct_value.name() {
                let (expected_ty, struct_ty) = match get_struct_ty(tcx, struct_name, named_types) {
                    Ok(struct_ty) => struct_ty,
                    Err(err) => {
                        errors.push(err, expr);
                        return;
                    }
                };

                unify_type(expected_ty, expr, errors);

                // Analyze fields
                let mut defined_fields = HashSet::new();

                for value_or_spread in struct_value.fields() {
                    match value_or_spread {
                        syntax::ValueFieldOrSpread::ValueField(field) => {
                            if defined_fields.contains(field.name()) {
                                errors.push(
                                    SemanticErrorKind::DuplicateStructField {
                                        name: field.name().to_string(),
                                        struct_ty: expected_ty,
                                    },
                                    expr,
                                );
                                continue;
                            }
                            defined_fields.insert(field.name());

                            let field_ty = if let Some(f) = struct_ty.get_field(field.name()) {
                                f.ty()
                            } else {
                                errors.push(
                                    SemanticErrorKind::UndefinedStructField {
                                        name: field.name().to_string(),
                                        struct_ty: expected_ty,
                                    },
                                    expr,
                                );
                                return;
                            };

                            analyze_expr(tcx, field.value(), vars, functions, named_types, errors);
                            unify_type(field_ty, field.value(), errors);
                        }
                        syntax::ValueFieldOrSpread::Spread(spread) => {
                            let operand = if let Some(operand) = spread.operand() {
                                operand
                            } else {
                                errors.push(SemanticErrorKind::EmptySpreadExpression, expr);
                                continue;
                            };

                            analyze_expr(tcx, operand, vars, functions, named_types, errors);
                            let ty = if let Some(ty) = operand.ty() {
                                ty
                            } else {
                                continue;
                            };

                            let fields = match ty.bottom_ty() {
                                Type::Struct(t) => t.fields(),
                                _ => {
                                    errors
                                        .push(SemanticErrorKind::InvalidSpreadOperand { ty }, expr);
                                    continue;
                                }
                            };

                            for tf in fields {
                                let expected_field_ty =
                                    if let Some(f) = struct_ty.get_field(tf.name()) {
                                        f.ty()
                                    } else {
                                        errors.push(
                                            SemanticErrorKind::UndefinedStructField {
                                                name: tf.name().to_string(),
                                                struct_ty: expected_ty,
                                            },
                                            expr,
                                        );
                                        return;
                                    };

                                if !expect_assignable_type(expected_field_ty, tf.ty(), expr, errors)
                                {
                                    continue;
                                }
                            }
                        }
                    }
                }
            } else {
                // Iterate over all initial fields and spread operators,
                // and analyze these sub-expressions. The result of merging
                // all these fields is then the type of the structure.
                let mut defined_fields: HashMap<&str, &Type<'tcx>> = HashMap::new();
                let mut value_fields = HashSet::new();

                for f in struct_value.fields() {
                    match f {
                        syntax::ValueFieldOrSpread::ValueField(field) => {
                            // Define by field can be only once.
                            if value_fields.contains(&field.name()) {
                                errors.push(
                                    SemanticErrorKind::DuplicateStructField {
                                        name: field.name().to_string(),
                                        struct_ty: tcx.empty_anon_struct_ty(),
                                    },
                                    expr,
                                );
                                continue;
                            }

                            analyze_expr(tcx, field.value(), vars, functions, named_types, errors);
                            let ty = if let Some(ty) = field.value().ty() {
                                ty
                            } else {
                                continue;
                            };

                            // If the value will be overridden, its type must be consistence.
                            if let Some(defined_ty) = defined_fields.get(&field.name()) {
                                if !expect_assignable_type(defined_ty, ty, expr, errors) {
                                    continue;
                                }
                            }
                            defined_fields.insert(field.name(), ty);
                            value_fields.insert(field.name());
                        }
                        syntax::ValueFieldOrSpread::Spread(spread) => {
                            let operand = if let Some(operand) = spread.operand() {
                                operand
                            } else {
                                errors.push(SemanticErrorKind::EmptySpreadExpression, expr);
                                continue;
                            };

                            analyze_expr(tcx, operand, vars, functions, named_types, errors);
                            let ty = if let Some(ty) = operand.ty() {
                                ty
                            } else {
                                continue;
                            };

                            if let Type::Struct(struct_ty) = ty.bottom_ty() {
                                for tf in struct_ty.fields() {
                                    // If the value will be overridden, its type must be consistence.
                                    if let Some(defined_ty) = defined_fields.get(&tf.name()) {
                                        if !expect_assignable_type(
                                            defined_ty,
                                            tf.ty(),
                                            expr,
                                            errors,
                                        ) {
                                            continue;
                                        }
                                    }
                                    defined_fields.insert(tf.name(), tf.ty());
                                }
                            } else {
                                errors.push(SemanticErrorKind::InvalidSpreadOperand { ty }, expr);
                            }
                        }
                    }
                }

                // Construct struct type
                let expected_tfs = defined_fields
                    .iter()
                    .map(|(k, ty)| TypedField::new(k.to_string(), ty))
                    .collect::<Vec<_>>();

                unify_type(tcx.anon_struct_ty(expected_tfs), expr, errors);
            }
        }
        &syntax::ExprKind::Minus(a) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);

            unify_type(tcx.int64(), a, errors);
            unify_type(tcx.int64(), expr, errors);
        }
        &syntax::ExprKind::Add(a, b)
        | &syntax::ExprKind::Sub(a, b)
        | &syntax::ExprKind::Mul(a, b)
        | &syntax::ExprKind::Div(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_type(tcx.int64(), a, errors);
            unify_type(tcx.int64(), b, errors);
            unify_type(tcx.int64(), expr, errors);
        }
        &syntax::ExprKind::Lt(a, b)
        | &syntax::ExprKind::Gt(a, b)
        | &syntax::ExprKind::Le(a, b)
        | &syntax::ExprKind::Ge(a, b)
        | &syntax::ExprKind::Eq(a, b)
        | &syntax::ExprKind::Ne(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_type(tcx.int64(), a, errors);
            unify_type(tcx.int64(), b, errors);
            unify_type(tcx.boolean(), expr, errors);
        }
        &syntax::ExprKind::And(a, b) | &syntax::ExprKind::Or(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_type(tcx.boolean(), a, errors);
            unify_type(tcx.boolean(), b, errors);
            unify_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::Var(name) => {
            if let Some(binding) = vars.get(name) {
                unify_type(binding.ty(), expr, errors);
            } else {
                errors.push(
                    SemanticErrorKind::UndefinedVariable { name: name.clone() },
                    expr,
                );
            }
        }
        &syntax::ExprKind::IndexAccess(operand, index) => {
            analyze_expr(tcx, operand, vars, functions, named_types, errors);

            let operand_ty = if let Some(ty) = operand.ty() {
                ty.bottom_ty()
            } else {
                return;
            };

            // index boundary check
            if let Type::Tuple(fs) = operand_ty {
                if index < fs.len() {
                    // apply type
                    unify_type(fs[index], expr, errors);
                    return;
                }
            }

            // If we have a value that is a union type, we can access elements
            // that are common to all types in the union. And the type of
            // a field can be a new union type too.
            //
            // For example:
            //
            //     type U = (int64,) | (string,)
            //     ...
            //     u.value # int64 | string
            if let Type::Union(member_types) = operand_ty {
                let common_field_types: Vec<_> = member_types
                    .iter()
                    .filter_map(|ty| ty.tuple_ty().and_then(|tuple_ty| tuple_ty.get(index)))
                    .copied()
                    .collect();
                if common_field_types.len() == member_types.len() {
                    // common field found. constructs the type for field.
                    let field_ty = tcx.union(common_field_types.into_iter());
                    unify_type(field_ty, expr, errors);
                    return;
                }
            }

            errors.push(
                SemanticErrorKind::FieldNotFound {
                    name: index.to_string(),
                    ty: operand_ty,
                },
                expr,
            );
        }
        syntax::ExprKind::FieldAccess(operand, name) => {
            analyze_expr(tcx, operand, vars, functions, named_types, errors);

            let operand_ty = if let Some(ty) = operand.ty() {
                ty.bottom_ty()
            } else {
                return;
            };

            // The field of struct type.
            if let Type::Struct(struct_ty) = operand_ty {
                if let Some(f) = struct_ty.get_field(name) {
                    // apply type
                    unify_type(f.ty(), expr, errors);
                    return;
                }
            }

            // If we have a value that is a union type, we can access members
            // that are common to all types in the union. And the type of
            // a field can be a new union type too.
            //
            // For example:
            //
            //     type U = { value: int64 } | { value: string }
            //     ...
            //     u.value # int64 | string
            if let Type::Union(member_types) = operand_ty {
                let common_field_types: Vec<_> = member_types
                    .iter()
                    .filter_map(|ty| {
                        ty.struct_ty()
                            .and_then(|struct_ty| struct_ty.get_field(name))
                    })
                    .map(|f| f.ty())
                    .collect();
                if common_field_types.len() == member_types.len() {
                    // common field found. constructs the type for field.
                    let field_ty = tcx.union(common_field_types.into_iter());
                    unify_type(field_ty, expr, errors);
                    return;
                }
            }

            errors.push(
                SemanticErrorKind::FieldNotFound {
                    name: name.to_string(),
                    ty: operand_ty,
                },
                expr,
            );
        }
        syntax::ExprKind::Call(call_expr) => {
            let caller_name = call_expr.name();
            let caller_args = call_expr.arguments();

            // At this point, the type of the argument is unknown.
            // First of all, determine the type of the argument if it is self-explanatory.
            for arg in caller_args {
                analyze_expr(tcx, arg, vars, functions, named_types, errors);
            }

            // Select the predefined function with the closest function signature based
            // on the function name and known argument types.
            // 1. function name
            // 2. The number of arguments
            // 3. Type of each parameter
            let name_matched = functions
                .iter()
                .filter(|f| f.name() == caller_name)
                .collect::<Vec<_>>();
            if name_matched.is_empty() {
                errors.push(
                    SemanticErrorKind::UndefinedFunction {
                        name: caller_name.to_string(),
                    },
                    expr,
                );
                return;
            }

            let n_args_matched = name_matched
                .iter()
                .filter(|f| f.params().len() == caller_args.len())
                .collect::<Vec<_>>();
            if n_args_matched.is_empty() {
                assert!(!name_matched.is_empty());
                errors.push(
                    SemanticErrorKind::WrongNumberOfArguments {
                        name: caller_name.to_string(),
                        expected: name_matched[0].params().len(),
                        actual: caller_args.len(),
                    },
                    expr,
                );
                return;
            }

            let mut ranked = n_args_matched
                .iter()
                .map(|f| {
                    let rank = caller_args
                        .iter()
                        .zip(f.params())
                        .fold(0, |rank, (arg, param)| {
                            if let Some(arg_ty) = arg.ty() {
                                // More restricted match, higher rank.
                                if arg_ty == param.ty() {
                                    rank + 2
                                } else if arg_ty.is_assignable_to(param.ty()) {
                                    rank + 1
                                } else {
                                    rank
                                }
                            } else {
                                rank
                            }
                        });

                    (rank, f)
                })
                .collect::<Vec<_>>();
            ranked.sort_by(|a, b| b.0.cmp(&a.0));
            assert!(!ranked.is_empty());

            if ranked.len() > 1 && ranked[0].0 == ranked[1].0 {
                let description = format!(
                    "{} and {}",
                    ranked[0].1.signature(),
                    ranked[1].1.signature()
                );

                errors.push(
                    SemanticErrorKind::MultipleCandidateFunctions { description },
                    expr,
                );
                return;
            }

            // Resolved overloaded function.
            let fun = ranked[0].1;
            let params = fun.params();

            assert!(fun.params().len() == caller_args.len());

            for (i, arg) in caller_args.iter().enumerate() {
                analyze_expr(tcx, arg, vars, functions, named_types, errors);
                unify_type(params[i].ty(), *arg, errors);
            }

            // The return type of the called function.
            if let Some(retty) = fun.retty() {
                unify_type(retty, expr, errors);
            } else {
                // The return type is undefined if the function is called before
                // defined (recursive function). In that case, we skip unification here and
                // assign the return type of the function in `analyze_call_sites_expr(...)`.
            }

            // Save
            call_expr.assign_function_signature(fun.signature());
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_expr(tcx, arg, vars, functions, named_types, errors);
            }
            unify_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_expr(tcx, head, vars, functions, named_types, errors);

            let head_ty = head
                .ty()
                .unwrap_or_else(|| panic!("Untyped head expression for {} - {:?}", head, head))
                .bottom_ty();

            // The result type of the expression.
            let mut expr_ty: Option<&Type> = None;

            for arm in arms {
                let mut scope = Scope::from_parent(vars);

                // Infer pattern's type and bindings
                analyze_pattern(
                    tcx,
                    arm.pattern(),
                    head_ty,
                    &mut scope,
                    functions,
                    named_types,
                    errors,
                );
                if !errors.is_empty() {
                    // Skip analyzing arm body if some errors occurred.
                    continue;
                }

                // -- Type narrowing
                // Override the named binding with new narrowed type binding.
                let context_ty = pattern_to_type(tcx, arm.pattern(), named_types);
                if let Some(narrowed_binding) = narrow_type(tcx, head, context_ty) {
                    scope.insert(narrowed_binding);
                }

                // unit type for empty body
                let arm_body_ty =
                    analyze_stmts(tcx, arm.body(), &mut scope, functions, named_types, errors);

                // -- Type widening
                // The types of every arm of the expression must be compatible,
                // and the type of the entire expression must be finally determined to be
                // one type. If the types of each arm contain literal types and they are not
                // compatible, then try to widen them to its general type.
                if let Some(ty1) = expr_ty {
                    if let Some(widen_ty) = widen_type(tcx, ty1, arm_body_ty) {
                        expr_ty = Some(widen_ty);
                    }
                }

                if let Some(expected_ty) = expr_ty {
                    expect_assignable_type(expected_ty, arm_body_ty, expr, errors);
                } else {
                    expr_ty = Some(arm_body_ty);
                }
            }

            if let Some(else_body) = else_body {
                let mut scope = Scope::from_parent(vars);

                let else_body_ty =
                    analyze_stmts(tcx, else_body, &mut scope, functions, named_types, errors);

                // Type widening
                if let Some(ty1) = expr_ty {
                    if let Some(widen_ty) = widen_type(tcx, ty1, else_body_ty) {
                        expr_ty = Some(widen_ty);
                    }
                }

                if let Some(expected_ty) = expr_ty {
                    expect_assignable_type(expected_ty, else_body_ty, expr, errors);
                } else {
                    expr_ty = Some(else_body_ty);
                }
            }

            if let Some(expr_ty) = expr_ty {
                unify_type(expr_ty, expr, errors);
            }

            if !errors.is_empty() {
                return;
            }

            // Usefulness check
            if let Err(err) = usefulness::check_match(head_ty, arms, else_body.is_some()) {
                errors.extend(err);
            }
        }
    }
}

fn analyze_let_pattern<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &syntax::Pattern<'nd, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    match pat.kind() {
        PatternKind::Var(_)
        | PatternKind::Wildcard
        | PatternKind::Integer(_)
        | PatternKind::Boolean(_)
        | PatternKind::String(_)
        | PatternKind::Tuple(_)
        | PatternKind::Struct(_) => {}
        PatternKind::Range { .. } | PatternKind::Or(..) => {
            unreachable!("Unsupported let pattern: `{}`", pat.kind());
        }
    }

    analyze_pattern(tcx, pat, expected_ty, vars, functions, named_types, errors);
}
#[allow(clippy::too_many_arguments)]
fn analyze_pattern_struct_fields<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    pattern_fields: &[syntax::PatternFieldOrSpread<'nd, 'tcx>],
    struct_fields: &'tcx [TypedField<'tcx>],
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    // Fields check
    // All fields must be covered or omitted by a spread pattern.
    let mut consumed_field_names = HashSet::new();
    let mut already_spread = false;

    for pat_field_or_spread in pattern_fields {
        match pat_field_or_spread {
            syntax::PatternFieldOrSpread::PatternField(field) => {
                if let Some(f) = struct_fields.iter().find(|tf| tf.name() == field.name()) {
                    if consumed_field_names.contains(&field.name()) {
                        errors.push(
                            SemanticErrorKind::DuplicateStructField {
                                name: field.name().to_string(),
                                struct_ty: expected_ty,
                            },
                            field,
                        );
                    } else {
                        analyze_pattern(
                            tcx,
                            field.pattern(),
                            f.ty().bottom_ty(),
                            vars,
                            functions,
                            named_types,
                            errors,
                        );
                        consumed_field_names.insert(field.name());
                    }
                } else {
                    errors.push(
                        SemanticErrorKind::UndefinedStructField {
                            name: field.name().to_string(),
                            struct_ty: expected_ty,
                        },
                        field,
                    );
                }
            }
            syntax::PatternFieldOrSpread::Spread(spread) => {
                if already_spread {
                    errors.push(
                        SemanticErrorKind::DuplicateSpreadPattern {
                            pattern: pat_field_or_spread.to_string(),
                        },
                        spread,
                    );
                }

                // Assign anonymous struct type to spread pattern.
                let rest_fields = struct_fields
                    .iter()
                    .filter(|f| !consumed_field_names.contains(&f.name()))
                    .cloned()
                    .collect();
                spread.assign_ty(tcx.anon_struct_ty(rest_fields));

                if let Some(spread_name) = spread.name() {
                    // Bind rest fields to the name.
                    if vars.get(spread_name).is_some() {
                        errors.push(
                            SemanticErrorKind::AlreadyBoundInPattern {
                                name: spread_name.to_string(),
                            },
                            spread,
                        );
                        return;
                    }

                    // New binding with rest fields.
                    let binding = Binding::new(spread_name.to_string(), spread.expect_ty());
                    vars.insert(binding);
                }

                already_spread = true;
            }
        }
    }

    if !already_spread && consumed_field_names.len() != struct_fields.len() {
        let names = struct_fields
            .iter()
            .filter(|f| !consumed_field_names.contains(f.name()))
            .map(|f| f.name().to_string())
            .collect();
        errors.push(
            SemanticErrorKind::UncoveredStructFields {
                names: FormatSymbols { names },
                struct_ty: expected_ty,
            },
            "",
        );
    }
}
fn analyze_pattern<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &syntax::Pattern<'nd, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Errors<'tcx>,
) {
    // Infer the type of pattern from its values.
    match pat.kind() {
        PatternKind::Integer(n) => {
            unify_type(tcx.literal_int64(*n), pat, errors);
        }
        PatternKind::Boolean(b) => {
            unify_type(tcx.literal_boolean(*b), pat, errors);
        }
        PatternKind::String(s) => {
            unify_type(tcx.literal_string(s.clone()), pat, errors);
        }
        PatternKind::Range { .. } => {
            unify_type(tcx.int64(), pat, errors);
        }
        PatternKind::Tuple(patterns) => {
            let sub_types = if let Type::Tuple(sub_types) = expected_ty {
                if sub_types.len() != patterns.len() {
                    errors.push(
                        SemanticErrorKind::MismatchedType {
                            expected: expected_ty,
                            actual: pattern_to_type(tcx, pat, named_types),
                        },
                        pat,
                    );
                    return;
                }
                sub_types
            } else {
                errors.push(
                    SemanticErrorKind::MismatchedType {
                        expected: expected_ty,
                        actual: pattern_to_type(tcx, pat, named_types),
                    },
                    pat,
                );
                return;
            };

            for (sub_pat, sub_ty) in patterns.iter().zip(sub_types.iter()) {
                analyze_pattern(tcx, sub_pat, sub_ty, vars, functions, named_types, errors);
            }

            unify_type(tcx.tuple(sub_types.clone()), pat, errors);
        }
        PatternKind::Struct(struct_pat) => {
            // Struct type check
            let struct_ty = if let Type::Struct(struct_ty) = expected_ty {
                struct_ty
            } else {
                errors.push(
                    SemanticErrorKind::MismatchedType {
                        expected: expected_ty,
                        actual: pattern_to_type(tcx, pat, named_types),
                    },
                    pat,
                );
                return;
            };

            // Named struct and unnamed struct
            if struct_ty.name() != struct_pat.name() {
                errors.push(
                    SemanticErrorKind::MismatchedType {
                        expected: expected_ty,
                        actual: pattern_to_type(tcx, pat, named_types),
                    },
                    pat,
                );
                return;
            }

            if !unify_type(expected_ty, pat, errors) {
                return;
            }

            // Fields check
            // All fields must be covered or omitted by a spread pattern.
            analyze_pattern_struct_fields(
                tcx,
                struct_pat.fields(),
                struct_ty.fields(),
                expected_ty,
                vars,
                functions,
                named_types,
                errors,
            );
        }
        PatternKind::Var(name) => {
            if vars.get(name).is_some() {
                errors.push(
                    SemanticErrorKind::AlreadyBoundInPattern { name: name.clone() },
                    pat,
                );
                return;
            }

            // We need the type of pattern.
            unify_type(expected_ty, pat, errors);

            let binding = Binding::new(name.to_string(), pat.expect_ty());
            vars.insert(binding);

            // already unified.
            return;
        }
        PatternKind::Or(sub_pats) => {
            let mut bindings: Option<HashMap<String, &Type>> = None;

            for sub_pat in sub_pats {
                // temporally introduce a new scope for a sub-pattern.
                let mut sub_vars = Scope::from_parent(vars);

                analyze_pattern(
                    tcx,
                    sub_pat,
                    expected_ty,
                    &mut sub_vars,
                    functions,
                    named_types,
                    errors,
                );

                // check new variables.
                let mut new_bindings = HashMap::new();
                let mut var_names = HashSet::new();

                for (name, b) in sub_vars.bindings_iter() {
                    new_bindings.insert(name.to_string(), b.ty());
                    var_names.insert(name);
                }

                // all new variable must be bound in all sub-patterns.
                if let Some(bindings) = &bindings {
                    for name in bindings.keys() {
                        var_names.insert(name);
                    }

                    for name in var_names {
                        match (bindings.get(name), new_bindings.get(name)) {
                            (None, Some(_)) | (Some(_), None) => {
                                // bound variable not found in this sub-pattern.
                                errors.push(
                                    SemanticErrorKind::UnboundVariableInSubPattern {
                                        name: name.to_string(),
                                    },
                                    pat,
                                );
                            }
                            (Some(expected_ty), Some(actual_ty)) => {
                                expect_assignable_type(expected_ty, actual_ty, pat, errors);
                            }
                            (None, None) => unreachable!(),
                        }
                    }
                }

                bindings = Some(new_bindings);
            }

            // Add bindings introduced in sub-patterns.
            if let Some(bindings) = bindings {
                for (var_name, var_ty) in bindings {
                    let binding = Binding::new(var_name, var_ty);
                    vars.insert(binding);
                }
            }
        }
        PatternKind::Wildcard => {}
    };

    unify_type(expected_ty, pat, errors);
}

fn analyze_call_sites_stmt<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    stmt: &syntax::Stmt<'nd, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
) {
    match stmt.kind() {
        &syntax::StmtKind::Let { rhs, .. } => {
            analyze_call_sites_expr(tcx, rhs, functions);
        }
        syntax::StmtKind::Expr(expr) => {
            analyze_call_sites_expr(tcx, expr, functions);
        }
    }
}
fn analyze_call_sites_expr<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &syntax::Expr<'nd, 'tcx>,
    functions: &[&syntax::Function<'nd, 'tcx>],
) {
    match expr.kind() {
        syntax::ExprKind::Call(call_expr) => {
            if expr.ty().is_none() {
                // The return type of callee function couldn't be inferred due to
                // recursive call or forward declaration. At this point, `functions` must
                // contain proper inferred function.
                let sig = call_expr.function_signature().unwrap();
                let fun = functions.iter().find(|f| f.signature() == sig).unwrap();
                expr.assign_ty(fun.retty().unwrap());
            }
            for arg in call_expr.arguments() {
                analyze_call_sites_expr(tcx, arg, functions);
            }
        }
        syntax::ExprKind::Tuple(values) => {
            for value in values {
                analyze_call_sites_expr(tcx, value, functions);
            }
        }
        syntax::ExprKind::Struct(struct_value) => {
            for value_or_spread in struct_value.fields() {
                match value_or_spread {
                    syntax::ValueFieldOrSpread::ValueField(field) => {
                        analyze_call_sites_expr(tcx, field.value(), functions);
                    }
                    syntax::ValueFieldOrSpread::Spread(spread) => {
                        if let Some(operand) = spread.operand() {
                            analyze_call_sites_expr(tcx, operand, functions);
                        }
                    }
                }
            }
        }
        &syntax::ExprKind::Minus(a) => {
            analyze_call_sites_expr(tcx, a, functions);
        }
        &syntax::ExprKind::Add(a, b)
        | &syntax::ExprKind::Sub(a, b)
        | &syntax::ExprKind::Mul(a, b)
        | &syntax::ExprKind::Div(a, b)
        | &syntax::ExprKind::Lt(a, b)
        | &syntax::ExprKind::Gt(a, b)
        | &syntax::ExprKind::Le(a, b)
        | &syntax::ExprKind::Ge(a, b)
        | &syntax::ExprKind::Eq(a, b)
        | &syntax::ExprKind::Ne(a, b)
        | &syntax::ExprKind::And(a, b)
        | &syntax::ExprKind::Or(a, b) => {
            analyze_call_sites_expr(tcx, a, functions);
            analyze_call_sites_expr(tcx, b, functions);
        }
        &syntax::ExprKind::IndexAccess(operand, _) => {
            analyze_call_sites_expr(tcx, operand, functions);
        }
        syntax::ExprKind::FieldAccess(operand, _) => {
            analyze_call_sites_expr(tcx, operand, functions);
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_call_sites_expr(tcx, arg, functions);
            }
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_call_sites_expr(tcx, head, functions);
            for arm in arms {
                for stmt in arm.body() {
                    analyze_call_sites_stmt(tcx, stmt, functions);
                }
            }

            if let Some(else_body) = else_body {
                for stmt in else_body {
                    analyze_call_sites_stmt(tcx, stmt, functions);
                }
            }
        }
        syntax::ExprKind::Integer(_)
        | syntax::ExprKind::Boolean(_)
        | syntax::ExprKind::String(_)
        | syntax::ExprKind::Var(_) => {}
    }
}

/// Try to widen a given type `ty1` to `ty2`, returns the widen if it exists.
fn widen_type<'tcx>(
    tcx: TypeContext<'tcx>,
    ty1: &'tcx Type<'tcx>,
    ty2: &'tcx Type<'tcx>,
) -> Option<&'tcx Type<'tcx>> {
    // TODO: widen the type to an union type.
    match (ty1, ty2) {
        (Type::Int64, Type::LiteralInt64(_)) | (Type::LiteralInt64(_), Type::Int64) => {
            Some(tcx.int64())
        }
        (Type::NativeInt, Type::LiteralInt64(_)) | (Type::LiteralInt64(_), Type::NativeInt) => {
            Some(tcx.native_int())
        }
        (Type::Boolean, Type::LiteralBoolean(_)) | (Type::LiteralBoolean(_), Type::Boolean) => {
            Some(tcx.boolean())
        }
        (Type::LiteralInt64(n0), Type::LiteralInt64(n1)) => {
            if n0 != n1 {
                Some(tcx.int64())
            } else {
                None
            }
        }
        (Type::String, Type::LiteralString(_)) | (Type::LiteralString(_), Type::String) => {
            Some(tcx.string())
        }
        (Type::LiteralString(s0), Type::LiteralString(s1)) => {
            if s0 != s1 {
                Some(tcx.string())
            } else {
                None
            }
        }
        // Recursively widen types in compound types
        (Type::Tuple(fs1), Type::Tuple(fs2)) => {
            if fs1.len() != fs2.len() {
                return None;
            }

            let value_types: Vec<_> = fs1
                .iter()
                .zip(fs2)
                .map(|(ty1, ty2)| widen_type(tcx, ty1, ty2).unwrap_or(ty2))
                .collect();
            Some(tcx.tuple(value_types))
        }
        (Type::Struct(struct_ty1), Type::Struct(struct_ty2)) => {
            if struct_ty1.name() != struct_ty2.name() {
                return None;
            }
            if struct_ty1.fields().len() != struct_ty2.fields().len() {
                return None;
            }

            let fields: Vec<_> = struct_ty1
                .fields()
                .iter()
                .zip(struct_ty2.fields())
                .map(|(f1, f2)| {
                    assert!(f1.name() == f2.name());
                    let ty = widen_type(tcx, f1.ty(), f2.ty()).unwrap_or_else(|| f1.ty());

                    TypedField::new(f1.name().to_string(), ty)
                })
                .collect();

            if let Some(struct_name) = struct_ty1.name() {
                Some(tcx.struct_ty(struct_name.to_string(), fields))
            } else {
                Some(tcx.anon_struct_ty(fields))
            }
        }
        _ => None,
    }
}

/// Narrow the type of given operand expression from contextual type (e.g. matched pattern).
fn narrow_type<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    target_expr: &'nd syntax::Expr<'nd, 'tcx>,
    context_type: &'tcx Type<'tcx>,
) -> Option<Binding<'tcx>> {
    let target_expr_ty = target_expr.ty()?.bottom_ty();

    // can be narrowed?
    if !target_expr_ty.can_be_narrowed_to(context_type) {
        return None;
    }

    // narrowing
    let binding_name;
    let mut node = target_expr;
    let mut narrowed_ty = context_type;

    loop {
        match node.kind() {
            syntax::ExprKind::Var(name) => {
                // root
                binding_name = name.to_string();
                break;
            }
            syntax::ExprKind::IndexAccess(operand, index) => {
                // narrow the type of x.N (x.0, x.1, ...)
                node = operand;
                match operand.expect_ty().bottom_ty() {
                    Type::Tuple(fs) => {
                        let mut value_types = fs.clone();

                        value_types.push(narrowed_ty);
                        value_types.swap_remove(*index);
                        narrowed_ty = tcx.tuple(value_types);
                    }
                    _ => unreachable!("expect tuple type"),
                }
            }
            syntax::ExprKind::FieldAccess(operand, field_name) => {
                // narrow the type of x.name
                node = operand;
                match operand.expect_ty().bottom_ty() {
                    Type::Struct(struct_ty) => {
                        let fields = struct_ty
                            .fields()
                            .iter()
                            .map(|f| {
                                if f.name() == field_name {
                                    TypedField::new(field_name.to_string(), narrowed_ty)
                                } else {
                                    TypedField::new(f.name().to_string(), f.ty())
                                }
                            })
                            .collect::<Vec<_>>();

                        if let Some(struct_name) = struct_ty.name() {
                            narrowed_ty = tcx.struct_ty(struct_name.to_string(), fields)
                        } else {
                            narrowed_ty = tcx.anon_struct_ty(fields)
                        }
                    }
                    _ => unreachable!("expect struct type"),
                }
            }
            _ => {
                return None;
            }
        }
    }

    Some(Binding::new(binding_name, narrowed_ty))
}

fn get_struct_ty<'tcx>(
    tcx: TypeContext<'tcx>,
    struct_name: &str,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
) -> Result<(&'tcx Type<'tcx>, &'tcx StructTy<'tcx>), SemanticErrorKind<'tcx>> {
    // Assign named struct type to struct value
    let expected_ty = if let Some(ty) = named_types.get(struct_name) {
        ty
    } else {
        return Err(SemanticErrorKind::UndefinedNamedType {
            name: struct_name.to_string(),
        });
    };

    if let Type::Struct(struct_ty) = expected_ty {
        Ok((expected_ty, struct_ty))
    } else {
        Err(SemanticErrorKind::MismatchedType {
            expected: tcx.empty_struct_ty(struct_name.to_string()),
            actual: expected_ty,
        })
    }
}

/// Infer the closest possible type from a given pattern.
fn pattern_to_type<'nd, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'nd syntax::Pattern<'nd, 'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
) -> &'tcx Type<'tcx> {
    match pat.kind() {
        PatternKind::Integer(n) => tcx.literal_int64(*n),
        PatternKind::Boolean(b) => tcx.literal_boolean(*b),
        PatternKind::String(s) => tcx.literal_string(s.clone()),
        PatternKind::Range { .. } => tcx.int64(),
        PatternKind::Tuple(patterns) => {
            let sub_types: Vec<_> = patterns
                .iter()
                .map(|pat| pattern_to_type(tcx, pat, named_types))
                .collect();

            tcx.tuple(sub_types)
        }
        PatternKind::Struct(struct_pat) => {
            // Search a named struct in the scope.
            if let Some(struct_name) = struct_pat.name() {
                if let Ok((ty, _)) = get_struct_ty(tcx, struct_name, named_types) {
                    return ty;
                }
            }

            // If not found corresponding struct, construct a new one from the pattern.
            let mut typed_fields = vec![];

            for f in struct_pat.fields() {
                if let syntax::PatternFieldOrSpread::PatternField(f) = f {
                    typed_fields.push(TypedField::new(
                        f.name().to_string(),
                        pattern_to_type(tcx, f.pattern(), named_types),
                    ));
                }
            }

            if let Some(struct_name) = struct_pat.name() {
                tcx.struct_ty(struct_name.to_string(), typed_fields)
            } else {
                tcx.anon_struct_ty(typed_fields)
            }
        }
        PatternKind::Var(_) | PatternKind::Wildcard => {
            pat.ty().unwrap_or_else(|| tcx.undetermined())
        }
        PatternKind::Or(patterns) => {
            let sub_types = patterns
                .iter()
                .map(|pat| pattern_to_type(tcx, pat, named_types));

            tcx.union(sub_types)
        }
    }
}
