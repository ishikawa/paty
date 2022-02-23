use super::inst::{Branch, Cond, Expr, ExprKind, FormatSpec, Function, Phi, Program, Stmt};
use crate::ty::TypeContext;
use typed_arena::Arena;

pub struct Optimizer<'a, 'tcx> {
    ctx: OptimizerPassContext<'a, 'tcx>,
}

impl<'a, 'tcx> Optimizer<'a, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'a Arena<Expr<'a, 'tcx>>,
        stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
    ) -> Self {
        let ctx = OptimizerPassContext {
            tcx,
            expr_arena,
            stmt_arena,
        };
        Self { ctx }
    }

    pub fn run_pass(&self, pass: &dyn OptimizerPass<'a, 'tcx>, program: &mut Program<'a, 'tcx>) {
        pass.optimize(&self.ctx, program)
    }

    pub fn run_function_pass(
        &self,
        pass: &dyn FunctionOptimizerPass<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
    ) {
        for fun in program.functions_mut() {
            pass.optimize_function(&self.ctx, fun);
        }
    }

    pub fn run_stmt_pass(
        &self,
        pass: &dyn StmtOptimizerPass<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
    ) {
        for fun in program.functions_mut() {
            let mut body = vec![];

            for stmt in &fun.body {
                if let Some(stmt) = pass.optimize_stmt(&self.ctx, stmt) {
                    body.push(stmt);
                }
            }
            fun.body = body;
        }
    }

    pub fn run_expr_stmt_pass(
        &self,
        pass: &dyn ExprOptimizerPass<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
    ) {
        for fun in program.functions_mut() {
            fun.body = self._run_expr_pass_with_stmts(pass, &fun.body);
        }
    }

    fn _run_expr_pass_with_stmts(
        &self,
        pass: &dyn ExprOptimizerPass<'a, 'tcx>,
        stmts: &[&'a Stmt<'a, 'tcx>],
    ) -> Vec<&'a Stmt<'a, 'tcx>> {
        let mut body = Vec::with_capacity(stmts.len());

        for stmt in stmts {
            body.push(self._run_expr_pass_with_stmt(pass, stmt));
        }
        body
    }

    fn _run_expr_pass_with_stmt(
        &self,
        pass: &dyn ExprOptimizerPass<'a, 'tcx>,
        stmt: &'a Stmt<'a, 'tcx>,
    ) -> &'a Stmt<'a, 'tcx> {
        match stmt {
            Stmt::TmpVarDef(def) => {
                if let Some(expr) = self._run_expr_pass_with_expr(pass, def.init()) {
                    return self
                        .ctx
                        .stmt_arena
                        .alloc(Stmt::TmpVarDef(def.with_init(expr)));
                }
            }
            Stmt::VarDef(def) => {
                if let Some(expr) = self._run_expr_pass_with_expr(pass, def.init()) {
                    return self.ctx.stmt_arena.alloc(Stmt::VarDef(def.with_init(expr)));
                }
            }
            Stmt::Phi(phi) => {
                if let Some(expr) = self._run_expr_pass_with_expr(pass, phi.value()) {
                    return self
                        .ctx
                        .stmt_arena
                        .alloc(Stmt::Phi(Phi::new(phi.var(), expr)));
                }
            }
            Stmt::Ret(ret) => {
                if let Some(expr) = self._run_expr_pass_with_expr(pass, ret) {
                    return self.ctx.stmt_arena.alloc(Stmt::Ret(expr));
                }
            }
            Stmt::Cond(cond) => {
                let branches = cond
                    .branches
                    .iter()
                    .map(|b| Branch {
                        condition: b
                            .condition
                            .and_then(|c| self._run_expr_pass_with_expr(pass, c).or(b.condition)),
                        body: self._run_expr_pass_with_stmts(pass, &b.body),
                    })
                    .collect();

                return self.ctx.stmt_arena.alloc(Stmt::Cond(Cond {
                    var: cond.var,
                    branches,
                }));
            }
        }

        stmt
    }

    fn _run_expr_pass_with_expr(
        &self,
        pass: &dyn ExprOptimizerPass<'a, 'tcx>,
        expr: &'a Expr<'a, 'tcx>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        if let Some(expr) = pass.optimize_expr(&self.ctx, expr) {
            // Don't optimize an expression recursively.
            return Some(expr);
        }

        // Optimize sub-expressions
        if let Some(kind) = self._run_expr_pass_with_expr_kind(pass, expr.kind()) {
            return Some(self.ctx.expr_arena.alloc(Expr::new(kind, expr.ty())));
        }

        None
    }

    fn _run_expr_pass_with_expr_kind(
        &self,
        pass: &dyn ExprOptimizerPass<'a, 'tcx>,
        kind: &ExprKind<'a, 'tcx>,
    ) -> Option<ExprKind<'a, 'tcx>> {
        match kind {
            &ExprKind::Minus(operand) => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::Minus(operand));
                }
            }
            ExprKind::Not(operand) => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::Not(operand));
                }
            }
            ExprKind::Add(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Add(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Sub(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Sub(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Mul(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Mul(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Div(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Div(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Eq(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Eq(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Ne(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Ne(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Lt(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Lt(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Le(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Le(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Gt(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Gt(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Ge(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Ge(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::And(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::And(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Or(a, b) => {
                let a2 = self._run_expr_pass_with_expr(pass, a);
                let b2 = self._run_expr_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Or(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Call { name, cc, args } => {
                let mut new_args = Vec::with_capacity(args.len());
                let mut modified = false;

                for arg in args {
                    if let Some(a) = self._run_expr_pass_with_expr(pass, arg) {
                        modified = true;
                        new_args.push(a);
                    } else {
                        new_args.push(arg);
                    }
                }
                if modified {
                    return Some(ExprKind::Call {
                        name: name.clone(),
                        cc: cc.clone(),
                        args: new_args,
                    });
                }
            }
            &ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => {
                let cond2 = self._run_expr_pass_with_expr(pass, cond);
                let then_value2 = self._run_expr_pass_with_expr(pass, then_value);
                let else_value2 = self._run_expr_pass_with_expr(pass, else_value);

                if cond2.is_some() || then_value2.is_some() || else_value2.is_some() {
                    return Some(ExprKind::CondValue {
                        cond: cond2.unwrap_or(cond),
                        then_value: then_value2.unwrap_or(then_value),
                        else_value: else_value2.unwrap_or(else_value),
                    });
                }
            }
            &ExprKind::CondAndAssign { cond, var } => {
                if let Some(cond) = cond.and_then(|c| self._run_expr_pass_with_expr(pass, c)) {
                    return Some(ExprKind::CondAndAssign {
                        cond: Some(cond),
                        var,
                    });
                }
            }
            ExprKind::Printf(args) => {
                let mut new_args = Vec::with_capacity(args.len());
                let mut modified = false;

                for arg in args {
                    match arg {
                        FormatSpec::Value(value) => {
                            if let Some(v) = self._run_expr_pass_with_expr(pass, value) {
                                modified = true;
                                new_args.push(FormatSpec::Value(v));
                            } else {
                                new_args.push(FormatSpec::Value(value));
                            }
                        }
                        FormatSpec::Quoted(value) => {
                            if let Some(v) = self._run_expr_pass_with_expr(pass, value) {
                                modified = true;
                                new_args.push(FormatSpec::Quoted(v));
                            } else {
                                new_args.push(FormatSpec::Quoted(value));
                            }
                        }
                        FormatSpec::Str(_) => {
                            new_args.push(arg.clone());
                        }
                    }
                }
                if modified {
                    return Some(ExprKind::Printf(new_args));
                }
            }
            ExprKind::Tuple(fs) => {
                let mut values = Vec::with_capacity(fs.len());
                let mut modified = false;

                for value in fs {
                    if let Some(v) = self._run_expr_pass_with_expr(pass, value) {
                        modified = true;
                        values.push(v);
                    } else {
                        values.push(value);
                    }
                }
                if modified {
                    return Some(ExprKind::Tuple(values));
                }
            }
            ExprKind::StructValue(fs) => {
                let mut value_fields = Vec::with_capacity(fs.len());
                let mut modified = false;

                for (name, value) in fs {
                    if let Some(v) = self._run_expr_pass_with_expr(pass, value) {
                        modified = true;
                        value_fields.push((name.clone(), v));
                    } else {
                        value_fields.push((name.clone(), value));
                    }
                }
                if modified {
                    return Some(ExprKind::StructValue(value_fields));
                }
            }
            &ExprKind::IndexAccess { operand, index } => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::IndexAccess { operand, index });
                }
            }
            ExprKind::FieldAccess { operand, name } => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::FieldAccess {
                        operand,
                        name: name.clone(),
                    });
                }
            }
            &ExprKind::UnionTag(operand) => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::UnionTag(operand));
                }
            }
            &ExprKind::UnionMemberAccess { operand, tag } => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::UnionMemberAccess { operand, tag });
                }
            }
            &ExprKind::PromoteToUnion { operand, tag } => {
                if let Some(operand) = self._run_expr_pass_with_expr(pass, operand) {
                    return Some(ExprKind::PromoteToUnion { operand, tag });
                }
            }
            ExprKind::TmpVar(var) => {
                if let Some(value) = var.immediate() {
                    if let Some(value) = self._run_expr_pass_with_expr(pass, value) {
                        var.set_immediate(value);
                    }
                }
            }
            ExprKind::Int64(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Var(_) => {}
        }

        None
    }
}

pub struct OptimizerPassContext<'a, 'tcx> {
    pub tcx: TypeContext<'tcx>,
    pub expr_arena: &'a Arena<Expr<'a, 'tcx>>,
    pub stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
}

pub trait OptimizerPass<'a, 'tcx> {
    fn optimize(&self, ctx: &OptimizerPassContext<'a, 'tcx>, program: &mut Program<'a, 'tcx>);
}

pub trait FunctionOptimizerPass<'a, 'tcx> {
    fn optimize_function(&self, ctx: &OptimizerPassContext<'a, 'tcx>, fun: &mut Function<'a, 'tcx>);
}

pub trait StmtOptimizerPass<'a, 'tcx> {
    /// Returns `None` if the stmt should be removed from function body.
    fn optimize_stmt(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        stmt: &'a Stmt<'a, 'tcx>,
    ) -> Option<&'a Stmt<'a, 'tcx>>;
}

pub trait ExprOptimizerPass<'a, 'tcx> {
    /// Returns `None` if the expression is not modified.
    fn optimize_expr(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        expr: &'a Expr<'a, 'tcx>,
    ) -> Option<&'a Expr<'a, 'tcx>>;
}

#[derive(Debug, Default)]
pub struct PruneUnusedTempVars {}

impl<'a, 'tcx> StmtOptimizerPass<'a, 'tcx> for PruneUnusedTempVars {
    fn optimize_stmt(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        stmt: &'a Stmt<'a, 'tcx>,
    ) -> Option<&'a Stmt<'a, 'tcx>> {
        self.prune_unused_stmt(ctx, stmt)
    }
}

impl<'a, 'tcx> PruneUnusedTempVars {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `None` if pruned
    fn prune_unused_stmt(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        stmt: &'a Stmt<'a, 'tcx>,
    ) -> Option<&'a Stmt<'a, 'tcx>> {
        match stmt {
            Stmt::TmpVarDef(def) => {
                if def.is_assignable() {
                    // We can remove a definition of a temporary variable which is assigned
                    // but never referred. To do this, however, we have to remove the assignment
                    // expression.
                    if def.var().used() == 0 {
                        return None;
                    }
                } else if def.var().used() == 1 || def.init().can_be_immediate() {
                    // This temporary variable is used only once, so it could be
                    // replaced with the expression.
                    def.var().set_immediate(def.init());
                    return None;
                }
            }
            Stmt::Phi(phi) => {
                if phi.var().used() == 0 {
                    // The result of cond expression is unused.
                    // So decrement the used count of a value because we increment it in
                    // Builder::build().
                    if Self::dcr_used_and_prunable(phi.value()) {
                        return None;
                    }
                }
            }
            Stmt::Cond(cond) => {
                let mut branches = vec![];
                for branch in &cond.branches {
                    let mut body = vec![];
                    for stmt in &branch.body {
                        if let Some(stmt) = self.prune_unused_stmt(ctx, stmt) {
                            body.push(stmt);
                        }
                    }
                    branches.push(Branch {
                        body,
                        condition: branch.condition,
                    })
                }

                let cond = Cond {
                    branches,
                    var: cond.var,
                };
                return Some(ctx.stmt_arena.alloc(Stmt::Cond(cond)));
            }
            _ => {}
        }
        Some(stmt)
    }

    fn dcr_used_and_prunable(expr: &Expr<'_, '_>) -> bool {
        if let ExprKind::TmpVar(t) = expr.kind() {
            return t.dcr_used() == 0 && t.immediate().is_none();
        }
        false
    }
}

#[derive(Debug, Default)]
pub struct ConcatAdjacentPrintf {}

impl<'a, 'tcx> FunctionOptimizerPass<'a, 'tcx> for ConcatAdjacentPrintf {
    fn optimize_function(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        fun: &mut Function<'a, 'tcx>,
    ) {
        // -- Peephole optimization.
        // Rewrite body
        let mut it = fun.body.iter().peekable();
        let mut body = vec![];

        // Combine consecutive printf(...) into one.
        let mut last_tmp_def = None;
        let mut format_specs = Vec::with_capacity(0);

        while let Some(&stmt) = it.next() {
            if let Stmt::TmpVarDef(t) = stmt {
                if t.var().used() == 0 {
                    if let ExprKind::Printf(args) = t.init().kind() {
                        format_specs.extend(args.clone());
                        last_tmp_def = Some(t);
                        if it.peek().is_some() {
                            continue;
                        }
                    }
                }
            }

            if !format_specs.is_empty() {
                let expr = Expr::printf(ctx.tcx, format_specs);
                format_specs = Vec::with_capacity(0);

                let init = ctx.expr_arena.alloc(expr);
                let d = last_tmp_def.unwrap().with_init(init);

                let stmt = &*ctx.stmt_arena.alloc(Stmt::TmpVarDef(d));
                body.push(stmt);
            }
            body.push(stmt);
        }

        // -- Rewrite body by cloning
        fun.body = body;
    }
}

impl<'a, 'tcx> ConcatAdjacentPrintf {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Replace an index access instruction with its tuple value if possible.
#[derive(Debug, Default)]
pub struct OptimizeIndexAccess {}

impl<'a, 'tcx> ExprOptimizerPass<'a, 'tcx> for OptimizeIndexAccess {
    fn optimize_expr(
        &self,
        _ctx: &OptimizerPassContext<'a, 'tcx>,
        expr: &'a Expr<'a, 'tcx>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        if let ExprKind::IndexAccess { operand, .. } = expr.kind() {
            if let ExprKind::TmpVar(_) = operand.kind() {
                //eprintln!("Found = {}", expr);
            }
        }

        None
    }
}

impl<'a, 'tcx> OptimizeIndexAccess {
    pub fn new() -> Self {
        Self::default()
    }
}
