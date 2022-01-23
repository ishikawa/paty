//! Semantic analysis
use self::error::SemanticError;
use crate::syntax::PatternKind;
use crate::{
    syntax,
    ty::{Type, TypeContext},
};
use std::collections::HashMap;

mod error;
mod usefulness;

#[derive(Debug)]
pub struct SemAST<'pcx, 'tcx> {
    expr: &'pcx syntax::Expr<'pcx, 'tcx>,
}

impl<'pcx, 'tcx> SemAST<'pcx, 'tcx> {
    pub fn new(expr: &'pcx syntax::Expr<'pcx, 'tcx>) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &'pcx syntax::Expr<'pcx, 'tcx> {
        self.expr
    }
}

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
}

// Analyze an AST and returns error if any.
pub fn analyze<'pcx: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &'pcx syntax::Expr<'pcx, 'tcx>,
) -> Result<SemAST<'pcx, 'tcx>, Vec<SemanticError<'tcx>>> {
    let mut errors = vec![];
    let mut scope = Scope::new();

    analyze_expr(tcx, expr, &mut scope, &mut Vec::new(), &mut errors);
    if errors.is_empty() {
        Ok(SemAST::new(expr))
    } else {
        Err(errors)
    }
}

fn unify_expr_type<'pcx: 'tcx, 'tcx>(
    expected: &'tcx Type<'tcx>,
    expr: &syntax::Expr<'pcx, 'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if let Some(actual) = expr.ty() {
        check_type(expected, actual, errors)
    } else {
        expr.assign_ty(expected);
        true
    }
}

fn unify_pat_type<'pcx: 'tcx, 'tcx>(
    expected: &'tcx Type<'tcx>,
    pat: &syntax::Pattern<'pcx, 'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if let Some(actual) = pat.ty() {
        check_type(expected, actual, errors)
    } else {
        pat.assign_ty(expected);
        true
    }
}

fn check_type<'tcx>(
    expected: &'tcx Type<'tcx>,
    actual: &'tcx Type<'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if actual != expected {
        errors.push(SemanticError::MismatchedType { expected, actual });
        false
    } else {
        true
    }
}

fn analyze_expr<'pcx: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &'pcx syntax::Expr<'pcx, 'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'pcx syntax::Function<'pcx, 'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
    match expr.kind() {
        syntax::ExprKind::Integer(_) => {
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Boolean(_) => {
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::String(_) => {
            unify_expr_type(tcx.string(), expr, errors);
        }
        syntax::ExprKind::Tuple(values) => {
            let mut value_types = vec![];

            for value in values {
                analyze_expr(tcx, value, vars, functions, errors);
                value_types.push(value.ty().unwrap());
            }

            unify_expr_type(tcx.tuple(&value_types), expr, errors);
        }
        syntax::ExprKind::Minus(a) => {
            analyze_expr(tcx, a, vars, functions, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b) => {
            analyze_expr(tcx, a, vars, functions, errors);
            analyze_expr(tcx, b, vars, functions, errors);

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
            analyze_expr(tcx, a, vars, functions, errors);
            analyze_expr(tcx, b, vars, functions, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), b, errors);
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::And(a, b) | syntax::ExprKind::Or(a, b) => {
            analyze_expr(tcx, a, vars, functions, errors);
            analyze_expr(tcx, b, vars, functions, errors);

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
        syntax::ExprKind::Let { pattern, rhs, then } => {
            analyze_expr(tcx, rhs, vars, functions, errors);

            match pattern.kind() {
                PatternKind::Variable(name) => {
                    let ty = rhs
                        .ty()
                        .unwrap_or_else(|| panic!("Untyped variable `{}` defined", name));
                    let binding = Binding::new(name, ty);
                    vars.insert(binding);
                }
                PatternKind::Integer(_)
                | PatternKind::Boolean(_)
                | PatternKind::String(_)
                | PatternKind::Range { .. }
                | PatternKind::Tuple(_)
                | PatternKind::Wildcard => {
                    unreachable!("Unsupported let pattern: `{}`", pattern.kind());
                }
            }

            analyze_expr(tcx, then, vars, functions, errors);
        }
        syntax::ExprKind::TupleField(operand, index) => {
            analyze_expr(tcx, operand, vars, functions, errors);

            // index boundary check
            let ty = operand.ty().unwrap();
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
        syntax::ExprKind::Call(name, args) => {
            if let Some(fun) = functions
                .iter()
                .rev()
                .find(|fun| fun.name() == name)
                .copied()
            {
                let params = fun.params();

                if params.len() != args.len() {
                    errors.push(SemanticError::WrongNumberOfArguments {
                        name: name.clone(),
                        expected: params.len(),
                        actual: args.len(),
                    });
                } else {
                    for (i, arg) in args.iter().enumerate() {
                        analyze_expr(tcx, arg, vars, functions, errors);
                        unify_expr_type(params[i].ty(), arg, errors);
                    }
                }

                // The return type is undefined if the function is called before
                // defined (recursive function).
                if let Some(retty) = fun.body().ty() {
                    unify_expr_type(retty, expr, errors);
                }
            } else {
                errors.push(SemanticError::UndefinedFunction { name: name.clone() });
            }
        }
        syntax::ExprKind::Puts(args) => {
            for arg in args {
                analyze_expr(tcx, arg, vars, functions, errors);
            }
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Fn(fun) => {
            // Function definition creates a new scope without a parent scope.
            let mut scope = Scope::new();

            functions.push(fun);
            {
                for param in fun.params() {
                    let binding = Binding::new(param.name(), param.ty());
                    scope.insert(binding);
                }

                let body = fun.body();

                analyze_expr(tcx, body, &mut scope, functions, errors);
                analyze_expr(tcx, fun.then(), vars, functions, errors);
            }
            functions.pop();
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_expr(tcx, head, vars, functions, errors);

            let head_ty = head
                .ty()
                .unwrap_or_else(|| panic!("Untyped head expression for {:?}", head));
            let mut expr_ty = None;

            for arm in arms {
                let mut scope = Scope::from_parent(vars);

                // Infer pattern's type and bindings
                //if !unify_pat_type(dbg!(head_ty), arm.pattern(), errors) {
                //    return;
                //}
                analyze_pattern(tcx, arm.pattern(), head_ty, &mut scope, functions, errors);
                analyze_expr(tcx, arm.body(), &mut scope, functions, errors);

                if let Some(expected) = expr_ty {
                    unify_expr_type(expected, arm.body(), errors);
                }

                expr_ty = Some(arm.body().ty().unwrap());
            }

            if let Some(else_body) = else_body {
                let mut scope = Scope::from_parent(vars);
                analyze_expr(tcx, else_body, &mut scope, functions, errors);

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

fn analyze_pattern<'pcx: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'pcx syntax::Pattern<'pcx, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'pcx syntax::Function<'pcx, 'tcx>>,
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
        PatternKind::String(_) => {
            unify_pat_type(tcx.string(), pat, errors);
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
                analyze_pattern(tcx, sub_pat, sub_ty, vars, functions, errors);
            }

            unify_pat_type(tcx.tuple(sub_types), pat, errors);
        }
        PatternKind::Variable(name) => {
            if vars.get(name).is_some() {
                errors.push(SemanticError::AlreadyBoundInPattern { name: name.clone() });
                return;
            }

            // We need the type of pattern.
            unify_pat_type(expected_ty, pat, errors);

            let binding = Binding::new(name, pat.expect_ty());

            vars.insert(binding);
        }
        PatternKind::Wildcard => {}
    };

    unify_pat_type(expected_ty, pat, errors);
}

fn pattern_to_type<'pcx: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    pat: &'pcx syntax::Pattern<'pcx, 'tcx>,
) -> &'tcx Type<'tcx> {
    // Infer the type of pattern from its values.
    match pat.kind() {
        PatternKind::Integer(_) => tcx.int64(),
        PatternKind::Boolean(_) => tcx.boolean(),
        PatternKind::String(_) => tcx.string(),
        PatternKind::Range { .. } => tcx.int64(),
        PatternKind::Tuple(patterns) => {
            let sub_types: Vec<_> = patterns
                .iter()
                .map(|pat| pattern_to_type(tcx, pat))
                .collect();

            tcx.tuple(&sub_types)
        }
        PatternKind::Variable(_) | PatternKind::Wildcard => tcx.undetermined(),
    }
}
