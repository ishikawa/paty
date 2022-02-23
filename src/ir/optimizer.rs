use super::inst::{Branch, Cond, Expr, ExprKind, Function, Program, Stmt};
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
    fn optimize_stmt(
        &self,
        ctx: &OptimizerPassContext<'a, 'tcx>,
        stmt: &'a Stmt<'a, 'tcx>,
    ) -> Option<&'a Stmt<'a, 'tcx>>;
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
        self._optimize_function(ctx, fun)
    }
}

impl<'a, 'tcx> ConcatAdjacentPrintf {
    pub fn new() -> Self {
        Self::default()
    }

    fn _optimize_function(
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
