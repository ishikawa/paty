use super::inst::{Branch, Cond, Expr, ExprKind, Function, Program, Stmt};
use crate::ty::TypeContext;
use typed_arena::Arena;

pub struct Optimizer<'a, 'tcx> {
    tcx: TypeContext<'tcx>,
    expr_arena: &'a Arena<Expr<'a, 'tcx>>,
    stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
}

impl<'a, 'tcx> Optimizer<'a, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'a Arena<Expr<'a, 'tcx>>,
        stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
    ) -> Self {
        Self {
            tcx,
            expr_arena,
            stmt_arena,
        }
    }

    pub fn optimize(&mut self, program: &mut Program<'a, 'tcx>) {
        for fun in program.functions_mut() {
            self.optimize_function(fun);
        }
    }

    fn optimize_function(&mut self, fun: &mut Function<'a, 'tcx>) {
        // Remove pruned stmts
        let mut body = vec![];

        for stmt in &fun.body {
            if let Some(stmt) = self.prune_unused_stmt(stmt) {
                body.push(stmt);
            }
        }

        // -- Peephole optimization.
        // Rewrite body
        let mut it = body.iter().peekable();
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
                let expr = Expr::printf(self.tcx, format_specs);
                format_specs = Vec::with_capacity(0);

                let init = self.expr_arena.alloc(expr);
                let d = last_tmp_def.unwrap().with_init(init);

                let stmt = &*self.stmt_arena.alloc(Stmt::TmpVarDef(d));
                body.push(stmt);
            }
            body.push(stmt);
        }

        // -- Rewrite body by cloning
        fun.body = body;
    }

    /// Returns `None` if pruned
    fn prune_unused_stmt(&mut self, stmt: &'a Stmt<'a, 'tcx>) -> Option<&'a Stmt<'a, 'tcx>> {
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
                    if dcr_used_and_prunable(phi.value()) {
                        return None;
                    }
                }
            }
            Stmt::Cond(cond) => {
                let mut branches = vec![];
                for branch in &cond.branches {
                    let mut body = vec![];
                    for stmt in &branch.body {
                        if let Some(stmt) = self.prune_unused_stmt(stmt) {
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
                return Some(self.stmt_arena.alloc(Stmt::Cond(cond)));
            }
            _ => {}
        }
        Some(stmt)
    }
}

fn dcr_used_and_prunable(expr: &Expr<'_, '_>) -> bool {
    if let ExprKind::TmpVar(t) = expr.kind() {
        return t.dcr_used() == 0 && t.immediate().is_none();
    }
    false
}
