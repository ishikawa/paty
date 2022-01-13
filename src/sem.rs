//! Semantic analysis
use self::error::SemanticError;
use crate::{
    syntax,
    ty::{Type, TypeContext},
};
use std::collections::HashMap;

mod error;
mod usefulness;

#[derive(Debug)]
pub struct SemAST<'a, 'tcx> {
    expr: &'a syntax::Expr<'tcx>,
}

impl<'a, 'tcx> SemAST<'a, 'tcx> {
    pub fn new(expr: &'a syntax::Expr<'tcx>) -> Self {
        Self { expr }
    }

    pub fn expr(&self) -> &syntax::Expr<'tcx> {
        self.expr
    }
}

#[derive(Debug)]
struct Binding<'tcx> {
    name: String,
    ty: &'tcx Type,
}

impl<'tcx> Binding<'tcx> {
    pub fn new(name: &str, ty: &'tcx Type) -> Self {
        Self {
            name: name.to_string(),
            ty,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type {
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
pub fn analyze<'a: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &'a syntax::Expr<'tcx>,
) -> Result<SemAST<'a, 'tcx>, Vec<SemanticError<'tcx>>> {
    let mut errors = vec![];
    let mut scope = Scope::new();

    analyze_loop(tcx, expr, &mut scope, &mut Vec::new(), &mut errors);
    if errors.is_empty() {
        Ok(SemAST::new(expr))
    } else {
        Err(errors)
    }
}

fn unify_expr_type<'tcx>(
    expected: &'tcx Type,
    expr: &syntax::Expr<'tcx>,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if let Some(actual) = expr.ty() {
        check_type(expected, actual, errors)
    } else {
        expr.assign_ty(expected);
        true
    }
}

fn check_type<'tcx>(
    expected: &'tcx Type,
    actual: &'tcx Type,
    errors: &mut Vec<SemanticError<'tcx>>,
) -> bool {
    if actual != expected {
        errors.push(SemanticError::MismatchedType { expected, actual });
        false
    } else {
        true
    }
}

fn analyze_loop<'a: 'tcx, 'tcx>(
    tcx: TypeContext<'tcx>,
    expr: &'a syntax::Expr<'tcx>,
    vars: &mut Scope<'_, 'tcx>,
    functions: &mut Vec<&'a syntax::Function<'tcx>>,
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
        syntax::ExprKind::Minus(a) => {
            analyze_loop(tcx, a, vars, functions, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Add(a, b)
        | syntax::ExprKind::Sub(a, b)
        | syntax::ExprKind::Mul(a, b)
        | syntax::ExprKind::Div(a, b)
        | syntax::ExprKind::Eq(a, b)
        | syntax::ExprKind::Ne(a, b) => {
            analyze_loop(tcx, a, vars, functions, errors);
            analyze_loop(tcx, b, vars, functions, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), b, errors);
            unify_expr_type(tcx.int64(), expr, errors);
        }
        syntax::ExprKind::Lt(a, b)
        | syntax::ExprKind::Gt(a, b)
        | syntax::ExprKind::Le(a, b)
        | syntax::ExprKind::Ge(a, b) => {
            analyze_loop(tcx, a, vars, functions, errors);
            analyze_loop(tcx, b, vars, functions, errors);

            unify_expr_type(tcx.int64(), a, errors);
            unify_expr_type(tcx.int64(), b, errors);
            unify_expr_type(tcx.boolean(), expr, errors);
        }
        syntax::ExprKind::And(a, b) | syntax::ExprKind::Or(a, b) => {
            analyze_loop(tcx, a, vars, functions, errors);
            analyze_loop(tcx, b, vars, functions, errors);

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
            analyze_loop(tcx, rhs, vars, functions, errors);

            let ty = rhs
                .ty()
                .unwrap_or_else(|| panic!("Untyped variable `{}` defined", name));
            let binding = Binding::new(name, ty);

            vars.insert(binding);
            analyze_loop(tcx, then, vars, functions, errors);
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
                        analyze_loop(tcx, arg, vars, functions, errors);
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
                analyze_loop(tcx, arg, vars, functions, errors);
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

                analyze_loop(tcx, body, &mut scope, functions, errors);
                analyze_loop(tcx, fun.then(), vars, functions, errors);
            }
            functions.pop();
        }
        syntax::ExprKind::Case {
            head,
            arms,
            else_body,
        } => {
            analyze_loop(tcx, head, vars, functions, errors);

            let head_ty = head
                .ty()
                .unwrap_or_else(|| panic!("Untyped head expression for {:?}", head));
            let mut expr_ty = None;

            for arm in arms {
                // pattern's type
                if !check_type(head_ty, arm.pattern().ty(), errors) {
                    return;
                }

                let mut scope = Scope::from_parent(vars);
                analyze_loop(tcx, arm.body(), &mut scope, functions, errors);

                if let Some(expected) = expr_ty {
                    unify_expr_type(expected, arm.body(), errors);
                }

                expr_ty = Some(arm.body().ty().unwrap());
            }

            if let Some(else_body) = else_body {
                let mut scope = Scope::from_parent(vars);
                analyze_loop(tcx, else_body, &mut scope, functions, errors);

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
