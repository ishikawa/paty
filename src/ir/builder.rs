use super::inst::{
    Branch, CallingConvention, Cond, Expr, ExprKind, FormatSpec, Function, Parameter, Program,
    Stmt, TmpVar, Var, VarDef,
};
use crate::syntax::{self, PatternKind, Typable};
use crate::ty::{expand_union_ty, FunctionSignature, StructTy, Type, TypeContext};
use std::collections::{HashMap, HashSet};
use typed_arena::Arena;

struct TmpVars<'a, 'tcx> {
    tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
}

impl<'a, 'tcx> TmpVars<'a, 'tcx> {
    pub fn new(tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>) -> Self {
        Self {
            tmp_var_arena,
            tmp_var_index: 0,
        }
    }

    pub fn next_temp_var(&mut self, ty: &'tcx Type<'tcx>) -> &'a TmpVar<'a, 'tcx> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t, ty, false))
    }

    pub fn next_control_flow_var(&mut self, tcx: &TypeContext<'tcx>) -> &'a TmpVar<'a, 'tcx> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena
            .alloc(TmpVar::new(t, tcx.boolean(), true))
    }
}

impl<'a, 'tcx> From<&TmpVars<'a, 'tcx>> for TmpVars<'a, 'tcx> {
    fn from(tmp_vars: &TmpVars<'a, 'tcx>) -> Self {
        Self {
            tmp_var_arena: tmp_vars.tmp_var_arena,
            tmp_var_index: 0,
        }
    }
}

pub struct Builder<'a, 'tcx> {
    tcx: TypeContext<'tcx>,
    // An arena allocators for instructions.
    expr_arena: &'a Arena<Expr<'a, 'tcx>>,
    stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
    tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
}

impl<'a, 'nd, 'tcx> Builder<'a, 'tcx> {
    pub fn new(
        tcx: TypeContext<'tcx>,
        expr_arena: &'a Arena<Expr<'a, 'tcx>>,
        stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,
        tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
    ) -> Self {
        Self {
            tcx,
            expr_arena,
            stmt_arena,
            tmp_var_arena,
        }
    }

    #[inline]
    fn tmp_var(&self, tmp_var: &'a TmpVar<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::tmp_var(tmp_var))
    }
    #[inline]
    fn usize(&self, value: usize) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::usize(self.tcx, value))
    }
    #[inline]
    fn not(&self, operand: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::not(self.tcx, operand))
    }
    #[inline]
    fn eq(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::eq(self.tcx, lhs, rhs))
    }
    #[inline]
    fn and(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::and(self.tcx, lhs, rhs))
    }
    #[inline]
    fn or(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::or(self.tcx, lhs, rhs))
    }
    #[inline]
    fn ge(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::ge(self.tcx, lhs, rhs))
    }
    #[inline]
    fn le(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::le(self.tcx, lhs, rhs))
    }
    #[inline]
    fn lt(&self, lhs: &'a Expr<'a, 'tcx>, rhs: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::lt(self.tcx, lhs, rhs))
    }
    #[inline]
    fn union_tag(&self, operand: &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::union_tag(self.tcx, operand))
    }
    #[inline]
    fn tuple_index_access(&self, operand: &'a Expr<'a, 'tcx>, index: usize) -> &'a Expr<'a, 'tcx> {
        self.expr_arena
            .alloc(Expr::tuple_index_access(operand, index))
    }
    #[inline]
    fn struct_field_access(&self, operand: &'a Expr<'a, 'tcx>, name: &str) -> &'a Expr<'a, 'tcx> {
        self.expr_arena
            .alloc(Expr::struct_field_access(operand, name))
    }
    #[inline]
    fn call_c(
        &self,
        name: String,
        args: Vec<&'a Expr<'a, 'tcx>>,
        retty: &'tcx Type<'tcx>,
    ) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Call {
            name,
            cc: CallingConvention::C,
            args,
        };
        self.expr_arena.alloc(Expr::new(kind, retty))
    }
    #[inline]
    fn int64(&self, value: i64) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::int64(self.tcx, value))
    }
    #[inline]
    fn native_int(&self, value: i64) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::native_int(self.tcx, value))
    }
    #[inline]
    fn bool(&self, value: bool) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::bool(self.tcx, value))
    }
    #[inline]
    fn const_string(&self, value: &str) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::const_string(self.tcx, value))
    }
    #[inline]
    fn cond_value(
        &self,
        cond: &'a Expr<'a, 'tcx>,
        then_value: &'a Expr<'a, 'tcx>,
        else_value: &'a Expr<'a, 'tcx>,
    ) -> &'a Expr<'a, 'tcx> {
        self.expr_arena
            .alloc(Expr::cond_value(cond, then_value, else_value))
    }
    #[inline]
    fn cond_and_assign(
        &self,
        cond: Option<&'a Expr<'a, 'tcx>>,
        var: &'a TmpVar<'a, 'tcx>,
    ) -> &'a Expr<'a, 'tcx> {
        self.expr_arena.alloc(Expr::new(
            ExprKind::CondAndAssign { cond, var },
            self.tcx.boolean(),
        ))
    }
    #[inline]
    fn union_member_access(
        &self,
        operand: &'a Expr<'a, 'tcx>,
        tag: usize,
        member_ty: &'tcx Type<'tcx>,
    ) -> &'a Expr<'a, 'tcx> {
        self.expr_arena
            .alloc(Expr::union_member_access(operand, tag, member_ty))
    }
    #[inline]
    fn var_def_stmt(&self, name: String, init: &'a Expr<'a, 'tcx>) -> &'a Stmt<'a, 'tcx> {
        let new_var_def = Stmt::VarDef(VarDef::new(name, init));
        self.stmt_arena.alloc(new_var_def)
    }
    #[inline]
    fn tmp_var_def_stmt(
        &self,
        tmp_var: &'a TmpVar<'a, 'tcx>,
        init: &'a Expr<'a, 'tcx>,
    ) -> &'a Stmt<'a, 'tcx> {
        let stmt = Stmt::tmp_var_def(tmp_var, init);
        self.stmt_arena.alloc(stmt)
    }

    pub fn build(&self, ast: &'nd [syntax::TopLevel<'nd, 'tcx>]) -> Program<'a, 'tcx> {
        let mut program = Program::new();
        let mut stmts: Vec<&'a Stmt<'a, 'tcx>> = vec![];
        let mut tmp_vars = TmpVars::new(self.tmp_var_arena);

        // Build top level statements and function definitions.
        for top_level in ast {
            match top_level {
                syntax::TopLevel::Declaration(decl) => {
                    self.build_decl(decl, &mut tmp_vars, &mut program, &mut stmts);
                }
                syntax::TopLevel::Stmt(stmt) => {
                    self.build_stmt(stmt, &mut tmp_vars, &mut program, &mut stmts);
                }
            }
        }

        // Add `return 0` statement for the entry point function if needed.
        if !matches!(stmts.last(), Some(Stmt::Ret(_))) {
            let ret = Stmt::Ret(self.native_int(0));
            stmts.push(self.stmt_arena.alloc(ret))
        }

        let signature = FunctionSignature::new("main".to_string(), vec![]);
        let main = Function {
            name: "main".to_string(),
            params: vec![],
            signature,
            body: stmts,
            retty: self.tcx.native_int(),
            is_entry_point: true,
        };
        program.push_function(main);
        program
    }

    fn push_expr(
        &self,
        expr: &'a Expr<'a, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let t = tmp_vars.next_temp_var(expr.ty());
        let stmt = Stmt::tmp_var_def(t, expr);
        stmts.push(self.stmt_arena.alloc(stmt));
        self.expr_arena.alloc(Expr::tmp_var(t))
    }

    fn push_expr_alloc(
        &self,
        expr: Expr<'a, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr = self.expr_arena.alloc(expr);
        self.push_expr(expr, tmp_vars, stmts)
    }

    fn push_expr_kind(
        &self,
        kind: ExprKind<'a, 'tcx>,
        expr_ty: &'tcx Type<'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        self.push_expr_alloc(Expr::new(kind, expr_ty), tmp_vars, stmts)
    }

    fn build_decl(
        &self,
        decl: &syntax::Declaration<'nd, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        _stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) {
        match decl.kind() {
            syntax::DeclarationKind::Function(syntax_fun) => {
                // save and reset temp var index
                let mut scoped_tmp_vars = TmpVars::from(&*tmp_vars);

                // convert parameter pattern to parameter name and assign variable.
                let mut params = vec![];
                let mut body_stmts = vec![];

                for p in syntax_fun.params() {
                    let pat = p.pattern();
                    let ty = pat.expect_ty();

                    // To emit anonymous types in type annotation.
                    program.add_decl_type(ty);

                    // Assign parameter names to be able to referenced later.
                    let param = match pat.kind() {
                        PatternKind::Var(name) => Parameter::Var(Var::new(name, ty)),
                        PatternKind::Wildcard => {
                            // ignore pattern but we have to define a parameter.
                            Parameter::TmpVar(scoped_tmp_vars.next_temp_var(ty))
                        }
                        PatternKind::Tuple(_) | PatternKind::Struct(_) => {
                            // Create a temporary parameter name to be able to referenced in the body.
                            // Simultaneously, we build deconstruct assignment expressions.
                            let t = scoped_tmp_vars.next_temp_var(ty);
                            let param_expr = self.expr_arena.alloc(Expr::tmp_var(t));

                            self._build_let_pattern(
                                pat,
                                param_expr,
                                &mut scoped_tmp_vars,
                                program,
                                &mut body_stmts,
                            );

                            Parameter::TmpVar(t)
                        }
                        PatternKind::Integer(_)
                        | PatternKind::Boolean(_)
                        | PatternKind::String(_)
                        | PatternKind::Range { .. }
                        | PatternKind::Or(..) => {
                            unreachable!("Unsupported let pattern: `{}`", p.pattern().kind());
                        }
                    };

                    params.push(param);
                }

                // Return value and type of the function
                let retty = syntax_fun.retty().expect("return type");
                program.add_decl_type(retty);

                let last_expr = syntax_fun
                    .body()
                    .iter()
                    .map(|stmt| {
                        self.build_stmt(stmt, &mut scoped_tmp_vars, program, &mut body_stmts)
                    })
                    .last()
                    .flatten();

                if let Some(last_expr) = last_expr {
                    let value =
                        self.promote_to(last_expr, retty, &mut scoped_tmp_vars, &mut body_stmts);
                    body_stmts.push(self.stmt_arena.alloc(Stmt::Ret(value)));
                }

                let fun = Function {
                    name: syntax_fun.name().to_string(),
                    params,
                    signature: syntax_fun.signature(),
                    body: body_stmts,
                    retty,
                    is_entry_point: false,
                };
                program.push_function(fun);
            }
            syntax::DeclarationKind::Struct(struct_def) => {
                program.add_decl_type(struct_def.ty());
            }
            syntax::DeclarationKind::TypeAlias(alias) => {
                program.add_decl_type(alias.ty());
            }
        }
    }

    fn build_stmt(
        &self,
        stmt: &syntax::Stmt<'nd, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        match stmt.kind() {
            syntax::StmtKind::Let { pattern, rhs } => {
                let init = self.build_expr(rhs, tmp_vars, program, stmts);
                self._build_let_pattern(pattern, init, tmp_vars, program, stmts);

                None
            }
            syntax::StmtKind::Expr(expr) => {
                let value = self.build_expr(expr, tmp_vars, program, stmts);
                Some(value)
            }
        }
    }

    fn build_expr(
        &self,
        expr: &'nd syntax::Expr<'nd, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr_ty = expr.expect_ty().bottom_ty();

        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                let kind = ExprKind::Int64(*n);
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Boolean(b) => {
                let kind = ExprKind::Bool(*b);
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::String(s) => {
                let kind = ExprKind::Str(s.clone());
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Tuple(sub_exprs) => {
                // Add tuple type to declaration types, because we have to
                // declare tuple type as a struct type in C.
                // However, the Zero-sized struct should not have a definition.
                program.add_decl_type(expr_ty);

                let tuple_fs = expr_ty.tuple_ty().unwrap();
                let mut values = vec![];

                for (sub, fty) in sub_exprs.iter().zip(tuple_fs) {
                    let value = self.build_expr(sub, tmp_vars, program, stmts);
                    let value = self.promote_to(value, fty, tmp_vars, stmts);
                    values.push(value);
                }

                let kind = ExprKind::Tuple(values);
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Struct(struct_value) => {
                let struct_ty = expr_ty.struct_ty().unwrap();
                if struct_value.name().is_none() {
                    // Add anonymous struct type to declaration types, because we have to
                    // declare a type as a struct type in C.
                    // However, the Zero-sized struct should not have a definition.
                    program.add_decl_type(expr_ty);
                }

                // Latter initializer can override previous initializers.
                // So generate initializer values in reversed order.
                let mut value_fields = vec![];
                let mut initialized_fields = HashSet::new();

                for field_or_spread in struct_value.fields().iter().rev() {
                    match field_or_spread {
                        syntax::ValueFieldOrSpread::ValueField(field) => {
                            if !initialized_fields.contains(&field.name()) {
                                let expected_field = struct_ty.get_field(field.name()).unwrap();

                                let value =
                                    self.build_expr(field.value(), tmp_vars, program, stmts);
                                let value =
                                    self.promote_to(value, expected_field.ty(), tmp_vars, stmts);

                                value_fields.push((field.name().to_string(), value));
                                initialized_fields.insert(field.name());
                            }
                        }
                        syntax::ValueFieldOrSpread::Spread(spread) => {
                            let operand = spread.expect_operand();
                            let fields = match operand.expect_ty() {
                                Type::Struct(struct_ty) => struct_ty.fields(),
                                _ => unreachable!("spread with invalid expr: {}", spread),
                            };
                            let built_spread_value = None;
                            for field in fields.iter().rev() {
                                if initialized_fields.contains(&field.name()) {
                                    // Overridden
                                    continue;
                                }

                                let spread_value = built_spread_value.unwrap_or_else(|| {
                                    self.build_expr(operand, tmp_vars, program, stmts)
                                });

                                let kind = ExprKind::FieldAccess {
                                    name: field.name().to_string(),
                                    operand: spread_value,
                                };
                                let expr = self.push_expr_kind(kind, field.ty(), tmp_vars, stmts);
                                value_fields.push((field.name().to_string(), expr));
                                initialized_fields.insert(field.name());
                            }
                        }
                    }
                }

                // Reversed -> Ordered
                value_fields.reverse();

                let kind = ExprKind::StructValue(value_fields);
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let kind = ExprKind::Minus(a);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Add(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Sub(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Mul(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Div(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Eq(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Ne(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Lt(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Gt(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Le(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Ge(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::And(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self.build_expr(a, tmp_vars, program, stmts);
                let b = self.build_expr(b, tmp_vars, program, stmts);
                let kind = ExprKind::Or(a, b);

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Var(name) => {
                let kind = ExprKind::Var(Var::new(name, expr_ty));
                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            &syntax::ExprKind::IndexAccess(operand, index) => {
                let expected_ty = expr_ty;
                let operand = self.build_expr(operand, tmp_vars, program, stmts);

                // expected_ty might be an auto generated union type.
                program.add_decl_type(expected_ty);

                match operand.ty().bottom_ty() {
                    Type::Tuple(_) => self.push_expr_alloc(
                        Expr::tuple_index_access(operand, index),
                        tmp_vars,
                        stmts,
                    ),
                    Type::Union(operand_member_types) => {
                        let operand_member_types = expand_union_ty(operand_member_types);
                        let union_tag = self.push_expr(self.union_tag(operand), tmp_vars, stmts);
                        let union_member_value = self.build_union_members_mapped_value(
                            operand,
                            &operand_member_types,
                            union_tag,
                            expected_ty,
                            |member_value| {
                                // Pre: member_value is a tuple value which have the element.
                                let access = self
                                    .expr_arena
                                    .alloc(Expr::tuple_index_access(member_value, index));
                                self.promote_to(access, expected_ty, tmp_vars, stmts)
                            },
                        );
                        self.push_expr(union_member_value, tmp_vars, stmts)
                    }
                    ty => unreachable!("unsupported type: {}", ty),
                }
            }
            syntax::ExprKind::FieldAccess(operand, name) => {
                let expected_ty = expr_ty;
                let operand = self.build_expr(operand, tmp_vars, program, stmts);

                // expected_ty might be an auto generated union type.
                program.add_decl_type(expected_ty);

                match operand.ty().bottom_ty() {
                    Type::Struct(_) => self.push_expr_alloc(
                        Expr::struct_field_access(operand, name),
                        tmp_vars,
                        stmts,
                    ),
                    Type::Union(operand_member_types) => {
                        let operand_member_types = expand_union_ty(operand_member_types);
                        let union_tag = self.push_expr(self.union_tag(operand), tmp_vars, stmts);
                        let union_member_value = self.build_union_members_mapped_value(
                            operand,
                            &operand_member_types,
                            union_tag,
                            expected_ty,
                            |member_value| {
                                // Pre: member_value is a struct value which have the field.
                                let access = self
                                    .expr_arena
                                    .alloc(Expr::struct_field_access(member_value, name));
                                self.promote_to(access, expected_ty, tmp_vars, stmts)
                            },
                        );
                        self.push_expr(union_member_value, tmp_vars, stmts)
                    }
                    ty => unreachable!("unsupported type: {}", ty),
                }
            }
            syntax::ExprKind::Call(call_expr) => {
                let sig = call_expr.function_signature().unwrap();
                let args = call_expr
                    .arguments()
                    .iter()
                    .zip(sig.params())
                    .map(|(arg, arg_ty)| {
                        let arg_expr = self.build_expr(arg, tmp_vars, program, stmts);
                        self.promote_to(arg_expr, arg_ty, tmp_vars, stmts)
                    })
                    .collect();
                let kind = ExprKind::Call {
                    name: call_expr.name().to_string(),
                    cc: CallingConvention::Std(sig),
                    args,
                };

                self.push_expr_kind(kind, expr_ty, tmp_vars, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                // Generates `printf(...)` code for each `puts(...)`.
                // It generates many `printf(...)` but these consequence `printf(...)`s will be
                // combined in the optimization phase.
                let mut it = args.iter().peekable();

                while let Some(arg) = it.next() {
                    let a = self.build_expr(arg, tmp_vars, program, stmts);
                    self.build_print_expr(a, false, tmp_vars, program, stmts);

                    // separated by a space
                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(" "), tmp_vars, stmts);
                    }
                }

                self._build_printf(FormatSpec::Str("\n"), tmp_vars, stmts)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = tmp_vars.next_temp_var(expr_ty);
                let t_head = self.build_expr(head, tmp_vars, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an condition and variable declarations from the pattern
                        let mut branch_stmts = vec![];

                        let condition = self.build_pattern(
                            t_head,
                            arm.pattern(),
                            tmp_vars,
                            program,
                            stmts,
                            &mut branch_stmts,
                        );

                        let mut ret = None;
                        for stmt in arm.body() {
                            ret = self.build_stmt(stmt, tmp_vars, program, &mut branch_stmts);
                        }
                        if let Some(ret) = ret {
                            let phi = Stmt::phi(t, ret);
                            branch_stmts.push(self.stmt_arena.alloc(phi));
                        }

                        Branch {
                            condition,
                            body: branch_stmts,
                        }
                    })
                    .collect::<Vec<_>>();

                if let Some(else_body) = else_body {
                    let mut branch_stmts = vec![];

                    let mut ret = None;
                    for stmt in else_body {
                        ret = self.build_stmt(stmt, tmp_vars, program, &mut branch_stmts);
                    }
                    if let Some(ret) = ret {
                        let phi = Stmt::phi(t, ret);
                        branch_stmts.push(self.stmt_arena.alloc(phi));
                    }

                    let branch = Branch {
                        condition: None,
                        body: branch_stmts,
                    };
                    branches.push(branch);
                } else if !branches.is_empty() {
                    // No explicit `else` arm for this `case` expression.

                    // TODO: the last arm of every `case` expression which was passed through usefulness
                    // check can be just a `else` arm if the condition doesn't contain any CFV.
                    //let i = branches.len() - 1;
                    //branches[i].condition = None;
                }

                let stmt = Stmt::Cond(Cond { branches, var: t });
                stmts.push(self.stmt_arena.alloc(stmt));

                self.expr_arena.alloc(Expr::tmp_var(t))
            }
        }
    }

    /// Type promotion
    fn promote_to(
        &self,
        operand: &'a Expr<'a, 'tcx>,
        expected_ty: &'tcx Type<'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let operand_ty = operand.ty().bottom_ty();
        let expected_ty = expected_ty.bottom_ty();

        match (operand_ty, expected_ty) {
            (Type::Union(operand_member_types), Type::Union(expected_member_types)) => {
                let operand_member_types = expand_union_ty(operand_member_types);
                let expected_member_types = expand_union_ty(expected_member_types);

                if operand_member_types == expected_member_types {
                    return operand;
                }

                let union_tag = self.push_expr(self.union_tag(operand), tmp_vars, stmts);
                let union_member_value = self.build_union_members_mapped_value(
                    operand,
                    &operand_member_types,
                    union_tag,
                    expected_ty,
                    |member_value| {
                        // Find an expected member type which is compatible with
                        // this member type. it must exist.
                        let member_ty = member_value.ty();
                        let (expected_tag, expected_member_ty) = expected_member_types
                            .iter()
                            .enumerate()
                            .find(|(_, ty)| member_ty.is_assignable_to(ty))
                            .unwrap_or_else(|| {
                                panic!(
                                    "an expected member type for {} must exist in {}",
                                    member_ty, expected_ty
                                );
                            });
                        let member_value =
                            self.promote_to(member_value, expected_member_ty, tmp_vars, stmts);

                        &*self.push_expr_alloc(
                            Expr::union_value(self.tcx, member_value, expected_tag, expected_ty),
                            tmp_vars,
                            stmts,
                        )
                    },
                );
                self.push_expr(union_member_value, tmp_vars, stmts)
            }
            (operand_ty, Type::Union(member_types)) => {
                let member_types = expand_union_ty(member_types);

                for (tag, mty) in member_types.iter().enumerate() {
                    if operand_ty.is_assignable_to(mty) {
                        let value = self.promote_to(operand, mty, tmp_vars, stmts);
                        let kind = ExprKind::UnionValue { value, tag };
                        return self.push_expr_kind(kind, expected_ty, tmp_vars, stmts);
                    }
                }
                unreachable!(
                    "no matched member type for union {} with operand: {}",
                    expected_ty, operand_ty
                );
            }
            (Type::Union(operand_member_types), expected_ty) => {
                let operand_member_types = expand_union_ty(operand_member_types);
                let union_tag = self.push_expr(self.union_tag(operand), tmp_vars, stmts);
                let union_member_value = self.build_union_members_mapped_value(
                    operand,
                    &operand_member_types,
                    union_tag,
                    expected_ty,
                    |member_value| self.promote_to(member_value, expected_ty, tmp_vars, stmts),
                );
                self.push_expr(union_member_value, tmp_vars, stmts)
            }
            // Unnamed types don't have a definition, so it must be promoted here.
            (Type::Struct(operand_struct_ty), Type::Struct(expected_struct_ty)) => {
                if expected_struct_ty.name().is_some() {
                    return operand;
                }
                if operand_struct_ty == expected_struct_ty {
                    return operand;
                }

                let promoted_fields = expected_struct_ty
                    .fields()
                    .iter()
                    .map(|f| {
                        let expr = Expr::struct_field_access(operand, f.name());
                        let expr = self.push_expr_alloc(expr, tmp_vars, stmts);
                        let value = self.promote_to(expr, f.ty(), tmp_vars, stmts);

                        (f.name().to_string(), value)
                    })
                    .collect();

                self.push_expr_kind(
                    ExprKind::StructValue(promoted_fields),
                    expected_ty,
                    tmp_vars,
                    stmts,
                )
            }
            (Type::Tuple(operand_fs), Type::Tuple(expected_fs)) => {
                if operand_fs == expected_fs {
                    return operand;
                }

                let m = expected_fs
                    .iter()
                    .enumerate()
                    .map(|(i, fty)| {
                        let expr = Expr::tuple_index_access(operand, i);
                        let expr = self.push_expr_alloc(expr, tmp_vars, stmts);
                        self.promote_to(expr, fty, tmp_vars, stmts)
                    })
                    .collect();
                self.push_expr_kind(ExprKind::Tuple(m), expected_ty, tmp_vars, stmts)
            }

            _ => operand,
        }
    }

    fn build_print_expr(
        &self,
        arg: &'a Expr<'a, 'tcx>,
        quote_string: bool,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        match arg.ty() {
            Type::Int64
            | Type::NativeInt
            | Type::Boolean
            | Type::LiteralInt64(_)
            | Type::LiteralBoolean(_) => {
                self._build_printf(FormatSpec::Value(arg), tmp_vars, stmts)
            }
            Type::String | Type::LiteralString(_) => {
                if quote_string {
                    self._build_printf(FormatSpec::Quoted(arg), tmp_vars, stmts)
                } else {
                    self._build_printf(FormatSpec::Value(arg), tmp_vars, stmts)
                }
            }
            Type::Tuple(fs) => {
                let mut it = fs.iter().enumerate().peekable();

                self._build_printf(FormatSpec::Str("("), tmp_vars, stmts);
                while let Some((i, sub_ty)) = it.next() {
                    let kind = ExprKind::IndexAccess {
                        operand: arg,
                        index: i,
                    };

                    let ir_expr = self.push_expr_kind(kind, sub_ty, tmp_vars, stmts);
                    self.build_print_expr(ir_expr, true, tmp_vars, program, stmts);

                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(", "), tmp_vars, stmts);
                    }
                }
                self._build_printf(FormatSpec::Str(")"), tmp_vars, stmts)
            }
            Type::Struct(struct_ty) => {
                if let Some(name) = struct_ty.name() {
                    self._build_printf(FormatSpec::Value(self.const_string(name)), tmp_vars, stmts);
                    self._build_printf(FormatSpec::Str(" "), tmp_vars, stmts);
                }

                // print typed fields
                let mut it = struct_ty.fields().iter().peekable();
                let empty = it.peek().is_none();

                self._build_printf(FormatSpec::Str("{"), tmp_vars, stmts);
                if !empty {
                    self._build_printf(FormatSpec::Str(" "), tmp_vars, stmts);
                }

                while let Some(f) = it.next() {
                    self._build_printf(
                        FormatSpec::Value(self.const_string(f.name())),
                        tmp_vars,
                        stmts,
                    );
                    self._build_printf(FormatSpec::Str(": "), tmp_vars, stmts);

                    let kind = ExprKind::FieldAccess {
                        operand: arg,
                        name: f.name().to_string(),
                    };

                    let ir_expr = self.push_expr_kind(kind, f.ty(), tmp_vars, stmts);
                    self.build_print_expr(ir_expr, true, tmp_vars, program, stmts);

                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(", "), tmp_vars, stmts);
                    }
                }

                if !empty {
                    self._build_printf(FormatSpec::Str(" "), tmp_vars, stmts);
                }
                self._build_printf(FormatSpec::Str("}"), tmp_vars, stmts)
            }
            Type::Union(member_types) => {
                let member_types = expand_union_ty(member_types);

                // For union type values, the appropriate value is output by
                // branching on the condition of the tag of the value.
                let t = tmp_vars.next_temp_var(self.tcx.int64());
                let union_tag = self.push_expr(self.union_tag(arg), tmp_vars, stmts);

                // generates branches
                let mut branches = vec![];
                for (tag, member_ty) in member_types.iter().enumerate() {
                    let mut branch_stmts = vec![];

                    // check union tag
                    let cond = self.eq(union_tag, self.usize(tag));

                    // print union member
                    let kind = ExprKind::UnionMemberAccess { operand: arg, tag };
                    let member = self.push_expr_alloc(
                        Expr::new(kind, member_ty),
                        tmp_vars,
                        &mut branch_stmts,
                    );

                    let ret = self.build_print_expr(
                        member,
                        quote_string,
                        tmp_vars,
                        program,
                        &mut branch_stmts,
                    );
                    let phi = Stmt::phi(t, ret);
                    branch_stmts.push(&*self.stmt_arena.alloc(phi));

                    branches.push(Branch {
                        condition: Some(cond),
                        body: branch_stmts,
                    });
                }

                let stmt = Stmt::Cond(Cond { branches, var: t });
                stmts.push(self.stmt_arena.alloc(stmt));

                self.expr_arena.alloc(Expr::tmp_var(t))
            }
            Type::Named(name) => unreachable!("untyped for the type named: {}", name),
            Type::Undetermined => unreachable!("untyped code"),
        }
    }
    fn _build_printf(
        &self,
        format_spec: FormatSpec<'a, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        self.push_expr_alloc(Expr::printf(self.tcx, vec![format_spec]), tmp_vars, stmts)
    }

    /// Returns condition expression for the pattern test.
    ///
    /// The pattern consists of the following elements
    ///
    /// ```ignore
    /// (variable) @ (pattern) : (type)
    /// ```
    ///
    /// When performing pattern matching, the following steps should be taken:
    ///
    /// 1. Test if the target value matches the type.
    /// 2. Next, test if it matches the pattern. If necessary, convert to a value matching the pattern type.
    /// 3. Bind to the variable.
    fn build_pattern(
        &self,
        target_expr: &'a Expr<'a, 'tcx>,
        pat: &'nd syntax::Pattern<'nd, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        outer_stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        // TODO: skip pattern test
        // type annotated pattern. If the pattern has an explicit type
        // annotation, the value is checked for type conformity, and if necessary,
        // the value is converted to that type.
        let (ty_cond, value_expr) = if let Some(explicit_ty) = pat.explicit_ty() {
            let cond = self._build_pattern_type_test(
                target_expr,
                explicit_ty,
                tmp_vars,
                program,
                outer_stmts,
                stmts,
            );
            let pat_ty = pat.expect_ty().bottom_ty();
            let value = self.promote_to(target_expr, pat_ty, tmp_vars, outer_stmts);

            program.add_decl_type(pat_ty);
            (cond, value)
        } else {
            (None, target_expr)
        };

        let pat_cond =
            self._build_pattern_test(value_expr, pat, tmp_vars, program, outer_stmts, stmts);

        [ty_cond, pat_cond]
            .iter()
            .filter_map(|c| *c)
            .reduce(|lhs, rhs| self.and(lhs, rhs))
    }
    fn _build_pattern_type_test(
        &self,
        target_expr: &'a Expr<'a, 'tcx>,
        pat_ty: &'tcx Type<'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        outer_stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        let target_ty = target_expr.ty().bottom_ty();
        let pat_ty = pat_ty.bottom_ty();
        assert!(pat_ty.is_assignable_to(target_ty));

        match (target_ty, pat_ty) {
            // literal types
            (Type::Int64 | Type::NativeInt, &Type::LiteralInt64(n)) => {
                Some(self.eq(target_expr, self.int64(n)))
            }
            (Type::Boolean, &Type::LiteralBoolean(b)) => {
                let cond = if b {
                    target_expr
                } else {
                    self.not(target_expr)
                };
                Some(cond)
            }
            (Type::String, Type::LiteralString(s)) => {
                let strcmp = self.call_c(
                    "strcmp".to_string(),
                    vec![target_expr, self.const_string(s)],
                    self.tcx.native_int(),
                );
                Some(self.eq(strcmp, self.native_int(0)))
            }
            (Type::Tuple(target_fs), Type::Tuple(pat_fs)) => {
                assert!(target_fs.len() == pat_fs.len());
                pat_fs
                    .iter()
                    .enumerate()
                    .filter_map(|(i, pat_ty)| {
                        let operand = self.tuple_index_access(target_expr, i);
                        self._build_pattern_type_test(
                            operand,
                            pat_ty,
                            tmp_vars,
                            program,
                            outer_stmts,
                            stmts,
                        )
                    })
                    .reduce(|lhs, rhs| self.and(lhs, rhs))
            }
            (Type::Struct(_), Type::Struct(pat_struct_ty)) => pat_struct_ty
                .fields()
                .iter()
                .filter_map(|field| {
                    let operand = self.struct_field_access(target_expr, field.name());
                    self._build_pattern_type_test(
                        operand,
                        field.ty(),
                        tmp_vars,
                        program,
                        outer_stmts,
                        stmts,
                    )
                })
                .reduce(|lhs, rhs| self.and(lhs, rhs)),
            (Type::Union(target_member_types), pat_ty) => {
                let target_member_types = expand_union_ty(target_member_types);

                target_member_types
                    .iter()
                    .enumerate()
                    .filter_map(|(tag, ty)| {
                        ty.is_assignable_to(pat_ty)
                            .then(|| self.eq(self.union_tag(target_expr), self.usize(tag)))
                    })
                    .reduce(|lhs, rhs| self.or(lhs, rhs))
            }
            (Type::Int64 | Type::NativeInt, Type::Int64 | Type::NativeInt)
            | (Type::Boolean, Type::Boolean)
            | (Type::String, Type::String) => None,
            _ => todo!("target_ty = {:?}, pat_ty = {:?}", target_ty, pat_ty),
        }
    }
    fn _build_pattern_test(
        &self,
        value_expr: &'a Expr<'a, 'tcx>,
        pat: &'nd syntax::Pattern<'nd, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        outer_stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        // TODO: Don't compute `cond_and_values` unless necessary.
        // TODO: Don't emit redundant condition check or optimize away these expressions.
        let cond_and_values: Vec<_> = if let Type::Union(member_types) = value_expr.ty().bottom_ty()
        {
            expand_union_ty(member_types)
                .iter()
                .enumerate()
                .map(|(tag, member_ty)| {
                    (
                        self.eq(self.union_tag(value_expr), self.usize(tag)),
                        self.union_member_access(value_expr, tag, member_ty),
                    )
                })
                .collect()
        } else {
            vec![(self.bool(true), value_expr)]
        };

        match pat.kind() {
            &PatternKind::Integer(n) => Some(self.eq(value_expr, self.int64(n))),
            &PatternKind::Boolean(b) => cond_and_values
                .iter()
                .map(|(cond, value)| match value.ty() {
                    &Type::LiteralBoolean(tb) => {
                        if b == tb {
                            cond
                        } else {
                            self.bool(false)
                        }
                    }
                    Type::Boolean => {
                        if b {
                            self.and(cond, value)
                        } else {
                            self.and(cond, self.not(value))
                        }
                    }
                    _ => self.bool(false),
                })
                .reduce(|lhs, rhs| self.or(lhs, rhs)),
            PatternKind::String(pat_str) => cond_and_values
                .iter()
                .map(|(cond, value)| match value.ty() {
                    Type::LiteralString(ty_str) => {
                        if pat_str == ty_str {
                            cond
                        } else {
                            self.bool(false)
                        }
                    }
                    Type::String => {
                        // Compare the value of head expression and pattern string with
                        // POSIX `strcmp` function.
                        let strcmp = self.call_c(
                            "strcmp".to_string(),
                            vec![value_expr, self.const_string(pat_str)],
                            self.tcx.native_int(),
                        );
                        let c = self.eq(strcmp, self.native_int(0));
                        self.and(cond, c)
                    }
                    _ => self.bool(false),
                })
                .reduce(|lhs, rhs| self.or(lhs, rhs)),
            &PatternKind::Range { lo, hi, end } => {
                let lo = self.int64(lo);
                let hi = self.int64(hi);

                let lhs = self.ge(value_expr, lo);
                let rhs = match end {
                    syntax::RangeEnd::Included => self.le(value_expr, hi),
                    syntax::RangeEnd::Excluded => self.lt(value_expr, hi),
                };

                Some(self.and(lhs, rhs))
            }
            PatternKind::Tuple(sub_pats) => {
                assert!(
                    !sub_pats.is_empty(),
                    "Empty tuple must be zero-sized type. It should be handled above."
                );

                sub_pats
                    .iter()
                    .enumerate()
                    .filter_map(|(i, pat)| {
                        let operand = self.tuple_index_access(value_expr, i);
                        self.build_pattern(operand, pat, tmp_vars, program, outer_stmts, stmts)
                    })
                    .reduce(|lhs, rhs| self.and(lhs, rhs))
            }
            PatternKind::Struct(struct_pat) => {
                assert!(
                    !struct_pat.fields().is_empty(),
                    "Empty struct must be zero-sized type. It should be handled above."
                );

                // Split fields into pattern fields and a spread.
                let mut pattern_fields = vec![];
                let mut spread_pat = None;

                for f in struct_pat.fields() {
                    match f {
                        syntax::PatternFieldOrSpread::PatternField(pf) => {
                            pattern_fields.push(pf);
                        }
                        syntax::PatternFieldOrSpread::Spread(spread) => {
                            assert!(spread_pat.is_none());
                            spread_pat = Some(spread);
                        }
                    }
                }
                if let Some(spread_pat) = spread_pat {
                    if let Some(spread_name) = spread_pat.name() {
                        let spread_ty = spread_pat.expect_ty();
                        program.add_decl_type(spread_ty);

                        let struct_ty = spread_pat.expect_struct_ty();
                        let values = self.struct_values(struct_ty, value_expr);
                        let struct_value = self
                            .expr_arena
                            .alloc(Expr::new(ExprKind::StructValue(values), spread_ty));

                        let var_def =
                            Stmt::VarDef(VarDef::new(spread_name.to_string(), struct_value));
                        stmts.push(self.stmt_arena.alloc(var_def));
                    }
                }

                pattern_fields
                    .iter()
                    .filter_map(|pat_field| {
                        let operand = self.struct_field_access(value_expr, pat_field.name());
                        self.build_pattern(
                            operand,
                            pat_field.pattern(),
                            tmp_vars,
                            program,
                            outer_stmts,
                            stmts,
                        )
                    })
                    .reduce(|lhs, rhs| self.and(lhs, rhs))
            }
            PatternKind::Var(name) => {
                let stmt = Stmt::VarDef(VarDef::new(name.clone(), value_expr));
                stmts.push(self.stmt_arena.alloc(stmt));
                None
            }
            PatternKind::Or(sub_pats) => {
                assert!(sub_pats.len() >= 2);

                let mut vars: HashMap<&str, Vec<(&Expr<'_, '_>, &VarDef<'_, '_>)>> = HashMap::new();
                let cond = sub_pats.iter().fold(None, |cond, sub_pat| {
                    // control flow variable
                    let cfv = tmp_vars.next_control_flow_var(&self.tcx);
                    let cfv_expr = self.tmp_var(cfv);

                    outer_stmts.push(self.tmp_var_def_stmt(cfv, self.bool(false)));

                    // build a sub pattern
                    let mut inner_stmts = vec![];
                    let sub_cond = self.build_pattern(
                        value_expr,
                        sub_pat,
                        tmp_vars,
                        program,
                        outer_stmts,
                        &mut inner_stmts,
                    );

                    // collects var definitions for this sub pattern for
                    // merging definitions across multiple sub patterns.
                    for stmt in inner_stmts {
                        if let Stmt::VarDef(def) = stmt {
                            if let Some(defs) = vars.get_mut(def.name()) {
                                defs.push((cfv_expr, def));
                            } else {
                                vars.insert(def.name(), vec![(cfv_expr, def)]);
                            }
                        } else {
                            unreachable!("stmt in branch must be var def, but was: {:?}", stmt);
                        }
                    }

                    let cond_and_assign = self.cond_and_assign(sub_cond, cfv);

                    if let Some(cond) = cond {
                        Some(self.or(cond, cond_and_assign))
                    } else {
                        Some(cond_and_assign)
                    }
                });

                // merge var definitions across multiple sub-patterns.
                for (name, defs) in vars {
                    assert!(!defs.is_empty());

                    // build a new type for the definition.
                    let def_ty = self.tcx.union(
                        defs.iter()
                            .map(|(_, d)| d.init().ty())
                            .collect::<Vec<_>>()
                            .as_slice(),
                    );
                    program.add_decl_type(def_ty);

                    let init = self.promote_to(defs[0].1.init(), def_ty, tmp_vars, stmts);
                    let init = defs.iter().fold(init, |else_value, (cfv_expr, var_def)| {
                        let then_value = self.promote_to(var_def.init(), def_ty, tmp_vars, stmts);
                        self.cond_value(cfv_expr, then_value, else_value)
                    });
                    stmts.push(self.var_def_stmt(name.to_string(), init));
                }

                cond
            }
            PatternKind::Wildcard => None,
        }
    }

    fn _build_let_pattern(
        &self,
        pattern: &'nd syntax::Pattern<'nd, 'tcx>,
        init: &'a Expr<'a, 'tcx>,
        tmp_vars: &mut TmpVars<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) {
        match pattern.kind() {
            PatternKind::Var(name) => {
                program.add_decl_type(pattern.expect_ty());

                let value = self.promote_to(init, pattern.expect_ty(), tmp_vars, stmts);
                let stmt = Stmt::VarDef(VarDef::new(name.to_string(), value));
                stmts.push(self.stmt_arena.alloc(stmt));
            }
            PatternKind::Wildcard => {
                // no bound variable to `_`
            }
            PatternKind::Tuple(fs) => {
                for (i, sub_pat) in fs.iter().enumerate() {
                    let kind = ExprKind::IndexAccess {
                        operand: init,
                        index: i,
                    };
                    let field = self.push_expr_kind(kind, sub_pat.expect_ty(), tmp_vars, stmts);
                    self._build_let_pattern(sub_pat, field, tmp_vars, program, stmts)
                }
            }
            PatternKind::Struct(struct_pat) => {
                for f in struct_pat.fields() {
                    match f {
                        syntax::PatternFieldOrSpread::PatternField(pat_field) => {
                            let kind = ExprKind::FieldAccess {
                                operand: init,
                                name: pat_field.name().to_string(),
                            };
                            let field = self.push_expr_kind(
                                kind,
                                pat_field.pattern().expect_ty(),
                                tmp_vars,
                                stmts,
                            );
                            self._build_let_pattern(
                                pat_field.pattern(),
                                field,
                                tmp_vars,
                                program,
                                stmts,
                            )
                        }
                        syntax::PatternFieldOrSpread::Spread(spread_pat) => {
                            if let Some(spread_name) = spread_pat.name() {
                                let spread_ty = spread_pat.expect_ty();
                                program.add_decl_type(spread_ty);

                                let struct_ty = spread_pat.expect_struct_ty();
                                let values = self.struct_values(struct_ty, init);
                                let struct_value = self
                                    .expr_arena
                                    .alloc(Expr::new(ExprKind::StructValue(values), spread_ty));

                                let def = Stmt::VarDef(VarDef::new(
                                    spread_name.to_string(),
                                    struct_value,
                                ));
                                stmts.push(self.stmt_arena.alloc(def));
                            }
                        }
                    }
                }
            }
            PatternKind::Integer(_)
            | PatternKind::Boolean(_)
            | PatternKind::String(_)
            | PatternKind::Range { .. }
            | PatternKind::Or(..) => {
                unreachable!("Unsupported let pattern: `{}`", pattern.kind());
            }
        };
    }

    fn struct_values(
        &self,
        struct_ty: &StructTy<'tcx>,
        init: &'a Expr<'a, 'tcx>,
    ) -> Vec<(String, &'a Expr<'a, 'tcx>)> {
        struct_ty
            .fields()
            .iter()
            .map(|f| {
                let kind = ExprKind::FieldAccess {
                    operand: init,
                    name: f.name().to_string(),
                };
                let v = self.expr_arena.alloc(Expr::new(kind, f.ty()));

                (f.name().to_string(), &*v)
            })
            .collect::<Vec<_>>()
    }

    /// Generates an expression that retrieves a value according to the tag of a union type operand.
    /// A conversion function can be specified.
    fn build_union_members_mapped_value<F>(
        &self,
        operand: &'a Expr<'a, 'tcx>,
        operand_member_types: &[&'tcx Type<'tcx>],
        operand_union_tag: &'a Expr<'a, 'tcx>,
        expected_ty: &'tcx Type<'tcx>,
        mut member_value_mapper: F,
    ) -> &'a Expr<'a, 'tcx>
    where
        F: FnMut(&'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx>,
    {
        // condition and value conversion.
        let vs: Vec<_> = operand_member_types
            .iter()
            .enumerate()
            .map(|(tag, member_ty)| {
                let value = self.expr_arena.alloc(Expr::usize(self.tcx, tag));
                let cond = self
                    .expr_arena
                    .alloc(Expr::eq(self.tcx, operand_union_tag, value));

                // member access
                let member_value = self
                    .expr_arena
                    .alloc(Expr::union_member_access(operand, tag, member_ty));

                let result = member_value_mapper(member_value);
                (&*cond, result)
            })
            .collect();

        // Constructs (?... :...) to initialize an union value.
        // Note, the last condition will be ignored as `else` condition because
        // the these conditions must be exhausted.
        assert!(!vs.is_empty());
        let cond_value_expr =
            vs.iter()
                .rev()
                .skip(1)
                .fold(vs.last().unwrap().1, |else_value, (cond, then_value)| {
                    let kind = ExprKind::CondValue {
                        cond,
                        then_value,
                        else_value,
                    };
                    self.expr_arena.alloc(Expr::new(kind, expected_ty))
                });

        cond_value_expr
    }
}
