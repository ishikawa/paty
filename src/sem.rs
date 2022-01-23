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
        syntax::ExprKind::Let { name, rhs, then } => {
            analyze_expr(tcx, rhs, vars, functions, errors);

            let ty = rhs
                .ty()
                .unwrap_or_else(|| panic!("Untyped variable `{}` defined", name));
            let binding = Binding::new(name, ty);

            vars.insert(binding);
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
                // pattern's type
                analyze_pattern(tcx, arm.pattern(), vars, functions, errors);

                if !unify_pat_type(head_ty, arm.pattern(), errors) {
                    return;
                }

                let mut scope = Scope::from_parent(vars);
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
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'pcx syntax::Function<'pcx, 'tcx>>,
    errors: &mut Vec<SemanticError<'tcx>>,
) {
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
            let mut sub_types = vec![];

            for sub_pat in patterns {
                analyze_pattern(tcx, sub_pat, vars, functions, errors);
                sub_types.push(sub_pat.ty().unwrap());
            }

            unify_pat_type(tcx.tuple(&sub_types), pat, errors);
        }
        PatternKind::Wildcard => {}
    }
}
