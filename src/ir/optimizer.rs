use super::inst::{Branch, Cond, Expr, ExprKind, FormatSpec, Phi, Program, Stmt};
use crate::ty::TypeContext;
use typed_arena::Arena;

pub struct Optimizer<'ir, 'tcx> {
    ctx: OptimizerPassContext<'ir, 'tcx>,
}

impl<'ir, 'tcx> Optimizer<'ir, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'ir Arena<Expr<'ir, 'tcx>>,
        stmt_arena: &'ir Arena<Stmt<'ir, 'tcx>>,
    ) -> Self {
        let ctx = OptimizerPassContext {
            tcx,
            expr_arena,
            stmt_arena,
        };
        Self { ctx }
    }

    pub fn run_function_pass(
        &self,
        pass: &dyn FunctionOptimizerPass<'ir, 'tcx>,
        program: &mut Program<'ir, 'tcx>,
    ) -> bool {
        let mut modified = false;

        for fun in program.functions_mut() {
            if let Some(body) = self._run_function_pass_with_stmts(pass, &fun.body) {
                fun.body = body;
                modified = true;
            }
        }
        if let Some(fun) = &mut program.entry_point {
            if let Some(body) = self._run_function_pass_with_stmts(pass, &fun.body) {
                fun.body = body;
                modified = true;
            }
        }

        modified
    }

    fn _run_function_pass_with_stmts(
        &self,
        pass: &dyn FunctionOptimizerPass<'ir, 'tcx>,
        stmts: &[&'ir Stmt<'ir, 'tcx>],
    ) -> Option<Vec<&'ir Stmt<'ir, 'tcx>>> {
        let mut modified = false;

        // Run stmts pass first
        let mut block = if let Some(block) = pass.optimize_stmts(&self.ctx, stmts) {
            modified = true;
            block
        } else {
            stmts.to_vec()
        };

        // Run pass with stmt and expr recursively.
        for i in (0..block.len()).rev() {
            match pass.optimize_stmt(&self.ctx, block[i]) {
                StmtOptimizerPassResult::Unmodified => {}
                StmtOptimizerPassResult::Modified(new_stmt) => {
                    modified = true;
                    block[i] = new_stmt;
                }
                StmtOptimizerPassResult::Eliminated => {
                    modified = true;
                    block.remove(i);
                }
            }
        }

        for stmt in &mut block {
            if let Some(new_stmt) = self._run_function_pass_with_stmt(pass, stmt) {
                modified = true;
                *stmt = new_stmt;
            }
        }

        modified.then(|| block)
    }

    fn _run_function_pass_with_stmt(
        &self,
        pass: &dyn FunctionOptimizerPass<'ir, 'tcx>,
        stmt: &'ir Stmt<'ir, 'tcx>,
    ) -> Option<&'ir Stmt<'ir, 'tcx>> {
        match stmt {
            Stmt::TmpVarDef(def) => {
                if let Some(expr) = self._run_function_pass_with_expr(pass, def.init()) {
                    return Some(
                        self.ctx
                            .stmt_arena
                            .alloc(Stmt::TmpVarDef(def.with_init(expr))),
                    );
                }
            }
            Stmt::VarDef(def) => {
                if let Some(expr) = self._run_function_pass_with_expr(pass, def.init()) {
                    return Some(self.ctx.stmt_arena.alloc(Stmt::VarDef(def.with_init(expr))));
                }
            }
            Stmt::Phi(phi) => {
                if let Some(expr) = self._run_function_pass_with_expr(pass, phi.value()) {
                    return Some(
                        self.ctx
                            .stmt_arena
                            .alloc(Stmt::Phi(Phi::new(phi.var(), expr))),
                    );
                }
            }
            Stmt::Ret(ret) => {
                if let Some(expr) = self._run_function_pass_with_expr(pass, ret) {
                    return Some(self.ctx.stmt_arena.alloc(Stmt::Ret(expr)));
                }
            }
            Stmt::Cond(cond) => {
                let mut branches_modified = false;
                let mut branches = Vec::with_capacity(cond.branches.len());

                for b in &cond.branches {
                    let condition = b.condition.and_then(|c| {
                        self._run_function_pass_with_expr(pass, c)
                            .map(|c| {
                                branches_modified = true;
                                c
                            })
                            .or(b.condition)
                    });
                    let body = self
                        ._run_function_pass_with_stmts(pass, &b.body)
                        .map(|stmts| {
                            branches_modified = true;
                            stmts
                        })
                        .unwrap_or_else(|| b.body.clone());
                    branches.push(Branch { condition, body });
                }

                if branches_modified {
                    return Some(self.ctx.stmt_arena.alloc(Stmt::Cond(Cond {
                        var: cond.var,
                        branches,
                    })));
                }
            }
        }

        None
    }

    fn _run_function_pass_with_expr(
        &self,
        pass: &dyn FunctionOptimizerPass<'ir, 'tcx>,
        expr: &'ir Expr<'ir, 'tcx>,
    ) -> Option<&'ir Expr<'ir, 'tcx>> {
        if let Some(expr) = pass.optimize_expr(&self.ctx, expr) {
            // Don't optimize an expression recursively.
            return Some(expr);
        }

        // Optimize sub-expressions
        if let Some(kind) = self._run_function_pass_with_expr_kind(pass, expr.kind()) {
            return Some(self.ctx.expr_arena.alloc(Expr::new(kind, expr.ty())));
        }

        None
    }

    fn _run_function_pass_with_expr_kind(
        &self,
        pass: &dyn FunctionOptimizerPass<'ir, 'tcx>,
        kind: &ExprKind<'ir, 'tcx>,
    ) -> Option<ExprKind<'ir, 'tcx>> {
        match kind {
            &ExprKind::Minus(operand) => {
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::Minus(operand));
                }
            }
            ExprKind::Not(operand) => {
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::Not(operand));
                }
            }
            ExprKind::Add(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Add(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Sub(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Sub(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Mul(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Mul(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Div(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Div(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Eq(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Eq(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Ne(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Ne(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Lt(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Lt(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Le(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Le(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Gt(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Gt(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Ge(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Ge(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::And(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::And(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Or(a, b) => {
                let a2 = self._run_function_pass_with_expr(pass, a);
                let b2 = self._run_function_pass_with_expr(pass, b);

                if a2.is_some() || b2.is_some() {
                    return Some(ExprKind::Or(a2.unwrap_or(a), b2.unwrap_or(b)));
                }
            }
            ExprKind::Call { name, cc, args } => {
                let mut new_args = Vec::with_capacity(args.len());
                let mut modified = false;

                for arg in args {
                    if let Some(a) = self._run_function_pass_with_expr(pass, arg) {
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
                let cond2 = self._run_function_pass_with_expr(pass, cond);
                let then_value2 = self._run_function_pass_with_expr(pass, then_value);
                let else_value2 = self._run_function_pass_with_expr(pass, else_value);

                if cond2.is_some() || then_value2.is_some() || else_value2.is_some() {
                    return Some(ExprKind::CondValue {
                        cond: cond2.unwrap_or(cond),
                        then_value: then_value2.unwrap_or(then_value),
                        else_value: else_value2.unwrap_or(else_value),
                    });
                }
            }
            &ExprKind::CondAndAssign { cond, var } => {
                if let Some(cond) = cond.and_then(|c| self._run_function_pass_with_expr(pass, c)) {
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
                            if let Some(v) = self._run_function_pass_with_expr(pass, value) {
                                modified = true;
                                new_args.push(FormatSpec::Value(v));
                            } else {
                                new_args.push(FormatSpec::Value(value));
                            }
                        }
                        FormatSpec::Quoted(value) => {
                            if let Some(v) = self._run_function_pass_with_expr(pass, value) {
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
                    if let Some(v) = self._run_function_pass_with_expr(pass, value) {
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
                    if let Some(v) = self._run_function_pass_with_expr(pass, value) {
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
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::IndexAccess { operand, index });
                }
            }
            ExprKind::FieldAccess { operand, name } => {
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::FieldAccess {
                        operand,
                        name: name.clone(),
                    });
                }
            }
            &ExprKind::UnionTag(operand) => {
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::UnionTag(operand));
                }
            }
            &ExprKind::UnionMemberAccess { operand, tag } => {
                if let Some(operand) = self._run_function_pass_with_expr(pass, operand) {
                    return Some(ExprKind::UnionMemberAccess { operand, tag });
                }
            }
            &ExprKind::UnionValue { value, tag } => {
                if let Some(value) = self._run_function_pass_with_expr(pass, value) {
                    return Some(ExprKind::UnionValue { value, tag });
                }
            }
            ExprKind::TmpVar(_)
            | ExprKind::Int64(_)
            | ExprKind::Bool(_)
            | ExprKind::Str(_)
            | ExprKind::Var(_) => {}
        }

        None
    }
}

pub struct OptimizerPassContext<'ir, 'tcx> {
    pub tcx: TypeContext<'tcx>,
    pub expr_arena: &'ir Arena<Expr<'ir, 'tcx>>,
    pub stmt_arena: &'ir Arena<Stmt<'ir, 'tcx>>,
}

pub trait FunctionOptimizerPass<'ir, 'tcx> {
    /// Returns `None` if statements are not modified.
    fn optimize_stmts(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        _stmts: &[&'ir Stmt<'ir, 'tcx>],
    ) -> Option<Vec<&'ir Stmt<'ir, 'tcx>>> {
        None
    }

    fn optimize_stmt(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        _stmt: &'ir Stmt<'ir, 'tcx>,
    ) -> StmtOptimizerPassResult<'ir, 'tcx> {
        StmtOptimizerPassResult::Unmodified
    }

    /// Returns `None` if the expression is not modified.
    fn optimize_expr(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        _expr: &'ir Expr<'ir, 'tcx>,
    ) -> Option<&'ir Expr<'ir, 'tcx>> {
        None
    }
}

pub enum StmtOptimizerPassResult<'ir, 'tcx> {
    Unmodified,
    /// A statement should be replaced with a new one.
    Modified(&'ir Stmt<'ir, 'tcx>),
    /// A statement should be remove from the function body.
    Eliminated,
}

/// Updates the initial value of all (immutable) temporary variables.
#[derive(Debug, Default)]
pub struct UpdateTmpVarValue {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for UpdateTmpVarValue {
    fn optimize_stmt(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        stmt: &'ir Stmt<'ir, 'tcx>,
    ) -> StmtOptimizerPassResult<'ir, 'tcx> {
        if let Stmt::TmpVarDef(def) = stmt {
            if !def.var().is_mutable() {
                def.var().set_value(def.init());
            }
        }

        StmtOptimizerPassResult::Unmodified
    }
}

/// Eliminates dead code
#[derive(Debug, Default)]
pub struct EliminateDeadStmts {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for EliminateDeadStmts {
    fn optimize_stmt(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        stmt: &'ir Stmt<'ir, 'tcx>,
    ) -> StmtOptimizerPassResult<'ir, 'tcx> {
        match stmt {
            Stmt::TmpVarDef(def) => {
                if def.var().is_mutable() {
                    // We can remove a definition of a temporary variable which is assigned
                    // but never referred. To do this, however, we have to remove the assignment
                    // expression.
                    if def.var().used() == 0 {
                        return StmtOptimizerPassResult::Eliminated;
                    }
                } else if def.var().used() == 0 && !def.init().has_side_effect() {
                    // dead code
                    return StmtOptimizerPassResult::Eliminated;
                }
            }
            Stmt::Phi(phi) => {
                if phi.var().used() == 0 {
                    // The result of cond expression is unused.
                    return StmtOptimizerPassResult::Eliminated;
                }
            }
            _ => {}
        }
        StmtOptimizerPassResult::Unmodified
    }
}

/// This is an optimization that merges consecutive `printf(...)`s into one.
#[derive(Debug, Default)]
pub struct ConcatAdjacentPrintf {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for ConcatAdjacentPrintf {
    fn optimize_stmts(
        &self,
        ctx: &OptimizerPassContext<'ir, 'tcx>,
        stmts: &[&'ir Stmt<'ir, 'tcx>],
    ) -> Option<Vec<&'ir Stmt<'ir, 'tcx>>> {
        // -- Peephole optimization.
        // Rewrite body
        let mut it = stmts.iter().peekable();
        let mut body = Vec::with_capacity(stmts.len());

        // Merge consecutive printf(...) into one.
        let mut last_tmp_def = None;
        let mut last_stmt;
        let mut format_specs = Vec::with_capacity(0);

        while let Some(&stmt) = it.next() {
            last_stmt = Some(stmt);

            if let Stmt::TmpVarDef(t) = stmt {
                if let ExprKind::Printf(args) = t.init().kind() {
                    // The statement is `t0 = @printf(...)`

                    // If the result of the statement is unused, we safely
                    // merge it into one. Otherwise, merging printf should be
                    // stopped here.
                    format_specs.extend(args.clone());
                    last_tmp_def = Some(t);
                    last_stmt = None;

                    if t.var().used() == 0 && it.peek().is_some() {
                        continue;
                    }
                }
            }

            if !format_specs.is_empty() {
                let expr = Expr::printf(ctx.tcx, format_specs);
                format_specs = Vec::with_capacity(0);

                let init = ctx.expr_arena.alloc(expr);
                let d = last_tmp_def.unwrap().with_init(init);

                let printf_stmt = &*ctx.stmt_arena.alloc(Stmt::TmpVarDef(d));
                body.push(printf_stmt);
            }
            if let Some(stmt) = last_stmt {
                body.push(stmt);
            }
        }

        Some(body)
    }
}

/// Remove redundant temporary variables by replacing variables with its value.
#[derive(Debug, Default)]
pub struct ReplaceRedundantTmpVars {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for ReplaceRedundantTmpVars {
    fn optimize_expr(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        expr: &'ir Expr<'ir, 'tcx>,
    ) -> Option<&'ir Expr<'ir, 'tcx>> {
        match expr.kind() {
            &ExprKind::IndexAccess { operand, index } => {
                if let ExprKind::TmpVar(t) = operand.kind() {
                    if let Some(v) = t.value() {
                        if let ExprKind::Tuple(fs) = v.kind() {
                            let fv = fs[index];
                            if fv.can_be_immediate() {
                                // Replace `t.N` access with direct tuple field.
                                t.dcr_used();
                                return Some(fv);
                            }
                        }
                    }
                }
            }
            ExprKind::FieldAccess { operand, name } => {
                if let ExprKind::TmpVar(t) = operand.kind() {
                    if let Some(value) = t.value() {
                        if let ExprKind::StructValue(values) = value.kind() {
                            if let Some((_, v)) = values.iter().find(|(k, _)| k == name) {
                                if v.can_be_immediate() {
                                    // Replace `t.N` access with direct tuple field.
                                    t.dcr_used();
                                    return Some(v);
                                }
                            }
                        }
                    }
                }
            }
            ExprKind::TmpVar(var) => {
                if var.is_mutable() {
                    // mutable variable shouldn't be replaced.
                    return None;
                }

                if let Some(value) = var.value() {
                    if value.can_be_immediate() || // value is immediate value.
                        // This temporary variable is used only once, so it could be
                        // replaced with the expression.
                        (var.used() == 1 && !value.has_side_effect())
                    {
                        var.dcr_used();
                        return Some(value);
                    }
                }
            }
            _ => {}
        }

        None
    }
}

/// Reset used count for a temporary variable.
#[derive(Debug, Default)]
pub struct ResetTmpVarUsed {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for ResetTmpVarUsed {
    fn optimize_expr(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        expr: &'ir Expr<'ir, 'tcx>,
    ) -> Option<&'ir Expr<'ir, 'tcx>> {
        if let &ExprKind::TmpVar(var) = expr.kind() {
            var.reset_used();
        }

        None
    }

    fn optimize_stmt(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        stmt: &'ir Stmt<'ir, 'tcx>,
    ) -> StmtOptimizerPassResult<'ir, 'tcx> {
        match stmt {
            Stmt::TmpVarDef(def) => def.var().reset_used(),
            Stmt::Phi(phi) => phi.var().reset_used(),
            _ => {}
        }
        StmtOptimizerPassResult::Unmodified
    }
}

/// Increments used count for a temporary variable.
#[derive(Debug, Default)]
pub struct MarkTmpVarUsed {}

impl<'ir, 'tcx> FunctionOptimizerPass<'ir, 'tcx> for MarkTmpVarUsed {
    fn optimize_expr(
        &self,
        _ctx: &OptimizerPassContext<'ir, 'tcx>,
        expr: &'ir Expr<'ir, 'tcx>,
    ) -> Option<&'ir Expr<'ir, 'tcx>> {
        if let &ExprKind::TmpVar(var) = expr.kind() {
            var.inc_used();
        }

        None
    }
}
