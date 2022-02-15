//! Semantic analysis
use self::error::{FormatSymbols, SemanticError};
use crate::syntax::{PatternKind, StmtKind};
use crate::ty::TypedField;
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
    pub fn new(name: &str, ty: &'tcx Type<'tcx>) -> Self {
        Self {
            name: name.to_string(),
            ty,
        }
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

// Analyze an AST and returns error if any.
pub fn analyze<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    body: &'nd [syntax::TopLevel<'nd, 'tcx>],
) -> Result<(), Vec<SemanticError<'tcx>>> {
    let mut errors = vec![];
    let mut scope = Scope::new();
    let mut named_types = HashMap::new();
    let mut functions: Vec<&'nd syntax::Function<'nd, 'tcx>> = vec![];

    // 1. Collect named types before analyze program.
    for top_level in body {
        if let syntax::TopLevel::Declaration(decl) = top_level {
            if let syntax::DeclarationKind::Struct(struct_decl) = decl.kind() {
                if named_types.contains_key(struct_decl.name()) {
                    errors.push(SemanticError::DuplicateNamedType {
                        name: struct_decl.name().to_string(),
                    });
                } else {
                    named_types.insert(struct_decl.name().to_string(), struct_decl.ty());
                }
            }
        }
    }

    // 2. For all struct declarations, resolve field types.
    for top_level in body {
        if let syntax::TopLevel::Declaration(decl) = top_level {
            if let syntax::DeclarationKind::Struct(struct_decl) = decl.kind() {
                resolve_type(tcx, struct_decl.ty(), &named_types, &mut errors);
            }
        }
    }

    // 3. For all function declarations, resolve parameter type and collection declarations.
    for top_level in body {
        if let syntax::TopLevel::Declaration(decl) = top_level {
            if let syntax::DeclarationKind::Function(fun) = decl.kind() {
                // Resolved parameter types before using it as key.
                for p in fun.params() {
                    resolve_type(tcx, p.ty(), &named_types, &mut errors);
                }

                let sig = fun.signature();

                if functions.iter().any(|f| f.signature() == sig) {
                    errors.push(SemanticError::DuplicateFunction { signature: sig });
                } else {
                    functions.push(fun);
                }
            }
        }
    }

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
                    &mut functions,
                    &mut named_types,
                    &mut errors,
                );
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn unify_expr_type<'nd: 'tcx, 'tcx>(
    expected: &'tcx Type<'tcx>,
    expr: &syntax::Expr<'nd, 'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if let Some(actual) = expr.ty() {
        expect_assignable_type(expected, actual, errors)
    } else {
        expr.assign_ty(expected);
        true
    }
}

fn unify_pat_type<'nd: 'tcx, 'tcx>(
    expected: &'tcx Type<'tcx>,
    pat: &syntax::Pattern<'nd, 'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if let Some(actual) = pat.ty() {
        expect_assignable_type(expected, actual, errors)
    } else {
        pat.assign_ty(expected);
        true
    }
}

fn expect_assignable_type<'tcx>(
    expected: &'tcx Type<'tcx>,
    actual: &'tcx Type<'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if !actual.is_assignable_to(expected) {
        errors.push(SemanticError::MismatchedType { expected, actual });
        false
    } else {
        true
    }
}

fn resolve_type<'tcx>(
    tcx: TypeContext<'tcx>,
    ty: &'tcx Type<'tcx>,
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
    match ty {
        Type::Tuple(fs) => {
            for fty in fs {
                resolve_type(tcx, fty, named_types, errors);
            }
        }
        Type::Struct(struct_ty) => {
            for f in struct_ty.fields() {
                resolve_type(tcx, f.ty(), named_types, errors);
            }
        }
        Type::Named(named_ty) => {
            if named_ty.ty().is_none() {
                if let Some(ty) = named_types.get(named_ty.name()) {
                    named_ty.assign_ty(ty);
                } else {
                    errors.push(SemanticError::UndefinedNamedType {
                        name: named_ty.name().to_string(),
                    })
                }
            }
        }
        Type::Int64
        | Type::Boolean
        | Type::String
        | Type::Undetermined
        | Type::NativeInt
        | Type::LiteralString(_) => {}
    }
}

fn analyze_decl<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    decl: &'nd syntax::Declaration<'nd, 'tcx>,
    _vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'nd syntax::Function<'nd, 'tcx>>,
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
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
                    errors.push(SemanticError::MismatchedReturnType {
                        signature: fun.signature(),
                        expected: retty,
                        actual: inferred_retty,
                    })
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
                errors.push(SemanticError::UnrecognizedReturnType {
                    signature: fun.signature(),
                });
            }
        };
    }
}

fn analyze_stmt<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    stmt: &syntax::Stmt<'nd, 'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'nd syntax::Function<'nd, 'tcx>>,
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
    match stmt.kind() {
        syntax::StmtKind::Let { pattern, rhs } => {
            analyze_expr(tcx, rhs, vars, functions, named_types, errors);
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
        syntax::StmtKind::Expr(expr) => {
            analyze_expr(tcx, expr, vars, functions, named_types, errors);
        }
    }
}

fn analyze_expr<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &'nd syntax::Expr<'nd, 'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&'nd syntax::Function<'nd, 'tcx>],
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
    match expr.kind() {
        syntax::ExprKind::Integer(_) => {
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Boolean(_) => {
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::String(s) => {
            //unify_expr_type(tcx.string(), expr, errors);
            unify_expr_type(tcx.literal_string(s.clone()), expr, errors);
        }
        syntax::ExprKind::Tuple(values) => {
            let mut value_types = vec![];

            for value in values {
                analyze_expr(tcx, value, vars, functions, named_types, errors);
                value_types.push(value.ty().unwrap());
            }

            unify_expr_type(tcx.tuple(&value_types), expr, errors);
        }
        syntax::ExprKind::Struct(struct_value) => {
            if let Some(struct_name) = struct_value.name() {
                // Assign named struct type to struct value
                let expected_ty = if let Some(ty) = named_types.get(struct_name) {
                    ty
                } else {
                    errors.push(SemanticError::UndefinedNamedType {
                        name: struct_name.to_string(),
                    });
                    return;
                };

                let struct_ty = if let Type::Struct(struct_ty) = expected_ty {
                    struct_ty
                } else {
                    errors.push(SemanticError::MismatchedType {
                        expected: tcx.empty_struct_ty(struct_name.to_string()),
                        actual: expected_ty,
                    });
                    return;
                };

                unify_expr_type(expected_ty, expr, errors);

                // Analyze fields
                let mut defined_fields = HashSet::new();

                for value_or_spread in struct_value.fields() {
                    match value_or_spread {
                        syntax::ValueFieldOrSpread::ValueField(field) => {
                            if defined_fields.contains(field.name()) {
                                errors.push(SemanticError::DuplicateStructField {
                                    name: field.name().to_string(),
                                    struct_ty: expected_ty,
                                });
                                continue;
                            }
                            defined_fields.insert(field.name());

                            let field_ty = if let Some(f) = struct_ty.get_field(field.name()) {
                                f.ty()
                            } else {
                                errors.push(SemanticError::UndefinedStructField {
                                    name: field.name().to_string(),
                                    struct_ty: expected_ty,
                                });
                                return;
                            };

                            analyze_expr(tcx, field.value(), vars, functions, named_types, errors);
                            unify_expr_type(field_ty, field.value(), errors);
                        }
                        syntax::ValueFieldOrSpread::Spread(spread) => {
                            let operand = if let Some(operand) = spread.operand() {
                                operand
                            } else {
                                errors.push(SemanticError::EmptySpreadExpression);
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
                                    errors.push(SemanticError::InvalidSpreadOperand { ty });
                                    continue;
                                }
                            };

                            for tf in fields {
                                let expected_field_ty =
                                    if let Some(f) = struct_ty.get_field(tf.name()) {
                                        f.ty()
                                    } else {
                                        errors.push(SemanticError::UndefinedStructField {
                                            name: tf.name().to_string(),
                                            struct_ty: expected_ty,
                                        });
                                        return;
                                    };

                                if !expect_assignable_type(expected_field_ty, tf.ty(), errors) {
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
                                errors.push(SemanticError::DuplicateStructField {
                                    name: field.name().to_string(),
                                    struct_ty: tcx.empty_anon_struct_ty(),
                                });
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
                                if !expect_assignable_type(defined_ty, ty, errors) {
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
                                errors.push(SemanticError::EmptySpreadExpression);
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
                                        if !expect_assignable_type(defined_ty, tf.ty(), errors) {
                                            continue;
                                        }
                                    }
                                    defined_fields.insert(tf.name(), tf.ty());
                                }
                            } else {
                                errors.push(SemanticError::InvalidSpreadOperand { ty });
                            }
                        }
                    }
                }

                // Construct struct type
                let expected_tfs = defined_fields
                    .iter()
                    .map(|(k, ty)| TypedField::new(k.to_string(), ty))
                    .collect::<Vec<_>>();

                unify_expr_type(tcx.anon_struct_ty(expected_tfs), expr, errors);
            }
        }
        syntax::ExprKind::Minus(a) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), b, errors);
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Lt(a, b)
        | syntax::ExprKind::Gt(a, b)
        | syntax::ExprKind::Le(a, b)
        | syntax::ExprKind::Ge(a, b)
        | syntax::ExprKind::Eq(a, b)
        | syntax::ExprKind::Ne(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), b, errors);
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::And(a, b) | syntax::ExprKind::Or(a, b) => {
            analyze_expr(tcx, a, vars, functions, named_types, errors);
            analyze_expr(tcx, b, vars, functions, named_types, errors);

            unify_expr_type(tcx.boolean(), a, errors);
            unify_expr_type(tcx.boolean(), b, errors);
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::Var(name) => {
            if let Some(binding) = vars.get(name) {
                unify_expr_type(binding.ty(), expr, errors);
            } else {
                errors.push(SemanticError::UndefinedVariable { name: name.clone() });
            }
        }
        syntax::ExprKind::IndexAccess(operand, index) => {
            analyze_expr(tcx, operand, vars, functions, named_types, errors);

            // index boundary check
            let ty = operand.expect_ty();
            if let Type::Tuple(fs) = ty {
                if *index < fs.len() {
                    // apply type
                    unify_expr_type(fs[*index], expr, errors);
                    return;
                }
            }

            errors.push(SemanticError::FieldNotFound {
                name: index.to_string(),
                ty,
            });
        }
        syntax::ExprKind::FieldAccess(operand, name) => {
            analyze_expr(tcx, operand, vars, functions, named_types, errors);
            if operand.ty().is_none() {
                return;
            }

            // index boundary check
            let ty = operand.expect_ty();

            if let Type::Struct(struct_ty) = ty {
                if let Some(f) = struct_ty.get_field(name) {
                    // apply type
                    unify_expr_type(f.ty(), expr, errors);
                    return;
                }
            }

            errors.push(SemanticError::FieldNotFound {
                name: name.to_string(),
                ty,
            });
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
                errors.push(SemanticError::UndefinedFunction {
                    name: caller_name.to_string(),
                });
                return;
            }

            let n_args_matched = name_matched
                .iter()
                .filter(|f| f.params().len() == caller_args.len())
                .collect::<Vec<_>>();
            if n_args_matched.is_empty() {
                assert!(!name_matched.is_empty());
                errors.push(SemanticError::WrongNumberOfArguments {
                    name: caller_name.to_string(),
                    expected: name_matched[0].params().len(),
                    actual: caller_args.len(),
                });
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

                errors.push(SemanticError::MultipleCandidateFunctions { description });
                return;
            }

            // Resolved overloaded function.
            let fun = ranked[0].1;
            let params = fun.params();

            assert!(fun.params().len() == caller_args.len());

            for (i, arg) in caller_args.iter().enumerate() {
                analyze_expr(tcx, arg, vars, functions, named_types, errors);
                unify_expr_type(params[i].ty(), arg, errors);
            }

            // The return type of the called function.
            if let Some(retty) = fun.retty() {
                unify_expr_type(retty, expr, errors);
            } else {
                // The return type is undefined if the function is called before
                // defined (recursive function). In that case, we skip unification here.
            }

            // Save
            call_expr.assign_function(fun);
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_expr(tcx, arg, vars, functions, named_types, errors);
            }
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_expr(tcx, head, vars, functions, named_types, errors);

            let head_ty = head
                .ty()
                .unwrap_or_else(|| panic!("Untyped head expression for {:?}", head))
                .bottom_ty();

            // The result type of the expression.
            let mut expr_ty: Option<&Type> = None;

            for arm in arms {
                let mut scope = Scope::from_parent(vars);

                // Infer pattern's type and bindings
                //if !unify_pat_type(dbg!(head_ty), arm.pattern(), errors) {
                //    return;
                //}
                analyze_pattern(
                    tcx,
                    arm.pattern(),
                    head_ty,
                    &mut scope,
                    functions,
                    named_types,
                    errors,
                );
                analyze_expr(tcx, arm.body(), &mut scope, functions, named_types, errors);

                // The type of every arms must be compatible.
                // If each type of arms is a literal type and they are incompatible,
                // try to widen the type to generic one.
                if let (Some(Type::LiteralString(s0)), Some(Type::LiteralString(s1))) =
                    (expr_ty, arm.body().ty())
                {
                    if s0 != s1 {
                        expr_ty = Some(tcx.string());
                    }
                }

                if let Some(expected_ty) = expr_ty {
                    unify_expr_type(expected_ty, arm.body(), errors);
                }

                if expr_ty.is_none() {
                    expr_ty = arm.body().ty().or_else(|| Some(tcx.undetermined()));
                }
            }

            if let Some(else_body) = else_body {
                let mut scope = Scope::from_parent(vars);
                analyze_expr(tcx, else_body, &mut scope, functions, named_types, errors);

                if let Some(expected) = expr_ty {
                    unify_expr_type(expected, else_body, errors);
                }

                expr_ty = Some(else_body.ty().unwrap());
            }

            unify_expr_type(expr_ty.unwrap(), expr, errors);

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

fn analyze_let_pattern<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'nd syntax::Pattern<'nd, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'nd syntax::Function<'nd, 'tcx>>,
    named_types: &mut HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
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
fn analyze_pattern_struct_fields<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pattern_fields: impl IntoIterator<Item = &'nd syntax::PatternFieldOrSpread<'nd, 'tcx>>,
    struct_fields: &'tcx [TypedField<'tcx>],
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&'nd syntax::Function<'nd, 'tcx>],
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
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
                        errors.push(SemanticError::DuplicateStructField {
                            name: field.name().to_string(),
                            struct_ty: expected_ty,
                        });
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
                    errors.push(SemanticError::UndefinedStructField {
                        name: field.name().to_string(),
                        struct_ty: expected_ty,
                    });
                }
            }
            syntax::PatternFieldOrSpread::Spread(spread) => {
                if already_spread {
                    errors.push(SemanticError::DuplicateSpreadPattern {
                        pattern: pat_field_or_spread.to_string(),
                    });
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
                        errors.push(SemanticError::AlreadyBoundInPattern {
                            name: spread_name.to_string(),
                        });
                        return;
                    }

                    // New binding with rest fields.
                    let binding = Binding::new(spread_name, spread.expect_ty());
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
        errors.push(SemanticError::UncoveredStructFields {
            names: FormatSymbols { names },
            struct_ty: expected_ty,
        });
    }
}

fn analyze_pattern<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'nd syntax::Pattern<'nd, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &[&'nd syntax::Function<'nd, 'tcx>],
    named_types: &HashMap<String, &'tcx Type<'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
    // Infer the type of pattern from its values.
    match pat.kind() {
        PatternKind::Integer(_) => {
            unify_pat_type(tcx.int64(), pat, errors);
        }
        PatternKind::Boolean(_) => {
            unify_pat_type(tcx.boolean(), pat, errors);
        }
        PatternKind::String(s) => {
            //unify_pat_type(tcx.string(), pat, errors);
            unify_pat_type(tcx.literal_string(s.clone()), pat, errors);
        }
        PatternKind::Range { .. } => {
            unify_pat_type(tcx.int64(), pat, errors);
        }
        PatternKind::Tuple(patterns) => {
            let sub_types = if let Type::Tuple(sub_types) = expected_ty {
                if sub_types.len() != patterns.len() {
                    errors.push(SemanticError::MismatchedType {
                        expected: expected_ty,
                        actual: pattern_to_type(tcx, pat),
                    });
                    return;
                }
                sub_types
            } else {
                errors.push(SemanticError::MismatchedType {
                    expected: expected_ty,
                    actual: pattern_to_type(tcx, pat),
                });
                return;
            };

            for (sub_pat, sub_ty) in patterns.iter().zip(sub_types.iter()) {
                analyze_pattern(tcx, sub_pat, sub_ty, vars, functions, named_types, errors);
            }

            unify_pat_type(tcx.tuple(sub_types), pat, errors);
        }
        PatternKind::Struct(struct_pat) => {
            // Struct type check
            let struct_ty = if let Type::Struct(struct_ty) = expected_ty {
                struct_ty
            } else {
                errors.push(SemanticError::MismatchedType {
                    expected: expected_ty,
                    actual: pattern_to_type(tcx, pat),
                });
                return;
            };

            // Named struct and unnamed struct
            if struct_ty.name() != struct_pat.name() {
                errors.push(SemanticError::MismatchedType {
                    expected: expected_ty,
                    actual: pattern_to_type(tcx, pat),
                });
                return;
            }

            if !unify_pat_type(expected_ty, pat, errors) {
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
                errors.push(SemanticError::AlreadyBoundInPattern { name: name.clone() });
                return;
            }

            // We need the type of pattern.
            unify_pat_type(expected_ty, pat, errors);

            let binding = Binding::new(name, pat.expect_ty());

            vars.insert(binding);
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
                                errors.push(SemanticError::UnboundVariableInSubPattern {
                                    name: name.to_string(),
                                });
                            }
                            (Some(expected_ty), Some(actual_ty)) => {
                                expect_assignable_type(expected_ty, actual_ty, errors);
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
                    let binding = Binding::new(&var_name, var_ty);
                    vars.insert(binding);
                }
            }
        }
        PatternKind::Wildcard => {}
    };

    unify_pat_type(expected_ty, pat, errors);
}

// Only used for error description
fn pattern_to_type<'nd: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'nd syntax::Pattern<'nd, 'tcx>,
) -> &'tcx Type<'tcx> {
    // Infer the type of pattern from its values.
    match pat.kind() {
        PatternKind::Integer(_) => tcx.int64(),
        PatternKind::Boolean(_) => tcx.boolean(),
        PatternKind::String(s) => {
            //tcx.string()
            tcx.literal_string(s.clone())
        }
        PatternKind::Range { .. } => tcx.int64(),
        PatternKind::Tuple(patterns) => {
            let sub_types: Vec<_> = patterns
                .iter()
                .map(|pat| pattern_to_type(tcx, pat))
                .collect();

            tcx.tuple(&sub_types)
        }
        PatternKind::Struct(struct_pat) => {
            let mut typed_fields = vec![];

            for f in struct_pat.fields() {
                if let syntax::PatternFieldOrSpread::PatternField(f) = f {
                    typed_fields.push(TypedField::new(
                        f.name().to_string(),
                        pattern_to_type(tcx, f.pattern()),
                    ));
                }
            }

            if let Some(struct_name) = struct_pat.name() {
                tcx.struct_ty(struct_name.to_string(), typed_fields)
            } else {
                tcx.anon_struct_ty(typed_fields)
            }
        }
        PatternKind::Or(sub_pats) => {
            // TODO: Union type?
            let sub_pat = sub_pats
                .first()
                .expect("or-pattern must have at least 2 elements.");
            pattern_to_type(tcx, sub_pat)
        }
        PatternKind::Var(_) | PatternKind::Wildcard => tcx.undetermined(),
    }
}
