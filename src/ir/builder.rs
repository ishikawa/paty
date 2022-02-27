use super::inst::{
    Branch, CallingConvention, Cond, Expr, ExprKind, FormatSpec, Function, Parameter, Program,
    Stmt, TmpVar, Var, VarDef,
};
use crate::syntax::{self, PatternKind, Typable};
use crate::ty::{FunctionSignature, StructTy, Type, TypeContext};
use std::collections::HashSet;
use typed_arena::Arena;

struct BuilderContext<'a, 'tcx> {
    tcx: TypeContext<'tcx>,
    // An arena allocators for instructions.
    expr_arena: &'a Arena<Expr<'a, 'tcx>>,
}

pub struct Builder<'a, 'tcx> {
    tcx: TypeContext<'tcx>,
    // An arena allocators for instructions.
    expr_arena: &'a Arena<Expr<'a, 'tcx>>,
    stmt_arena: &'a Arena<Stmt<'a, 'tcx>>,

    tmp_var_arena: &'a Arena<TmpVar<'a, 'tcx>>,
    /// The current index of temporary variables. It starts from 0 and
    /// incremented by creating a new temporary variable. This index will
    /// be saved and reset to 0 when function enter, and restored when function exit.
    tmp_var_index: usize,
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
            tmp_var_index: 0,
        }
    }

    fn builder_context(&self) -> BuilderContext<'a, 'tcx> {
        BuilderContext {
            tcx: self.tcx,
            expr_arena: self.expr_arena,
        }
    }

    pub fn build(&mut self, ast: &'nd [syntax::TopLevel<'nd, 'tcx>]) -> Program<'a, 'tcx> {
        let mut program = Program::new();
        let mut stmts: Vec<&'a Stmt<'a, 'tcx>> = vec![];

        // Build top level statements and function definitions.
        for top_level in ast {
            match top_level {
                syntax::TopLevel::Declaration(decl) => {
                    self.build_decl(decl, &mut program, &mut stmts);
                }
                syntax::TopLevel::Stmt(stmt) => {
                    self.build_stmt(stmt, &mut program, &mut stmts);
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

    fn next_temp_var(&mut self, ty: &'tcx Type<'tcx>) -> &'a TmpVar<'a, 'tcx> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena.alloc(TmpVar::new(t, ty, false))
    }

    fn next_control_flow_var(&mut self) -> &'a TmpVar<'a, 'tcx> {
        let t = self.tmp_var_index;
        self.tmp_var_index += 1;
        self.tmp_var_arena
            .alloc(TmpVar::new(t, self.tcx.boolean(), true))
    }

    fn push_expr(
        &mut self,
        expr: &'a Expr<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let t = self.next_temp_var(expr.ty());
        let stmt = Stmt::tmp_var_def(t, expr);
        stmts.push(self.stmt_arena.alloc(stmt));
        self.expr_arena.alloc(Expr::tmp_var(t))
    }

    fn push_expr_alloc(
        &mut self,
        expr: Expr<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr = self.expr_arena.alloc(expr);
        self.push_expr(expr, stmts)
    }

    fn push_expr_kind(
        &mut self,
        kind: ExprKind<'a, 'tcx>,
        expr_ty: &'tcx Type<'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        self.push_expr_alloc(Expr::new(kind, expr_ty), stmts)
    }

    fn native_int(&self, value: i64) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Int64(value);
        let ty = self.tcx.native_int();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    #[allow(unused)]
    fn bool(&self, value: bool) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Bool(value);
        let ty = self.tcx.boolean();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    fn const_string(&self, value: &str) -> &'a Expr<'a, 'tcx> {
        let kind = ExprKind::Str(value.to_string());
        let ty = self.tcx.string();

        self.expr_arena.alloc(Expr::new(kind, ty))
    }

    fn build_decl(
        &mut self,
        decl: &syntax::Declaration<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        _stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) {
        match decl.kind() {
            syntax::DeclarationKind::Function(syntax_fun) => {
                // save and reset temp var index
                let saved_tmp_var_index = self.tmp_var_index;
                self.tmp_var_index = 0;

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
                            Parameter::TmpVar(self.next_temp_var(ty))
                        }
                        PatternKind::Tuple(_) | PatternKind::Struct(_) => {
                            // Create a temporary parameter name to be able to referenced in the body.
                            // Simultaneously, we build deconstruct assignment expressions.
                            let t = self.next_temp_var(ty);
                            let param_expr = self.expr_arena.alloc(Expr::tmp_var(t));

                            self._build_let_pattern(pat, param_expr, program, &mut body_stmts);

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
                    .map(|stmt| self.build_stmt(stmt, program, &mut body_stmts))
                    .last()
                    .flatten();

                if let Some(last_expr) = last_expr {
                    let value = self.promote_to(last_expr, retty, &mut body_stmts);
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

                // restore
                self.tmp_var_index = saved_tmp_var_index;
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
        &mut self,
        stmt: &syntax::Stmt<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        match stmt.kind() {
            syntax::StmtKind::Let { pattern, rhs } => {
                let init = self.build_expr(rhs, program, stmts);
                self._build_let_pattern(pattern, init, program, stmts);

                None
            }
            syntax::StmtKind::Expr(expr) => {
                let value = self.build_expr(expr, program, stmts);
                Some(value)
            }
        }
    }

    fn build_expr(
        &mut self,
        expr: &'nd syntax::Expr<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let expr_ty = expr.expect_ty().bottom_ty();

        match expr.kind() {
            syntax::ExprKind::Integer(n) => {
                let kind = ExprKind::Int64(*n);
                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Boolean(b) => {
                let kind = ExprKind::Bool(*b);
                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::String(s) => {
                let kind = ExprKind::Str(s.clone());
                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Tuple(sub_exprs) => {
                // Add tuple type to declaration types, because we have to
                // declare tuple type as a struct type in C.
                // However, the Zero-sized struct should not have a definition.
                program.add_decl_type(expr_ty);

                let tuple_fs = expr_ty.tuple_ty().unwrap();
                let mut values = vec![];

                for (sub, fty) in sub_exprs.iter().zip(tuple_fs) {
                    let value = self.build_expr(sub, program, stmts);
                    let value = self.promote_to(value, fty, stmts);
                    values.push(value);
                }

                let kind = ExprKind::Tuple(values);
                self.push_expr_kind(kind, expr_ty, stmts)
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

                                let value = self.build_expr(field.value(), program, stmts);
                                let value = self.promote_to(value, expected_field.ty(), stmts);

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

                                let spread_value = built_spread_value
                                    .unwrap_or_else(|| self.build_expr(operand, program, stmts));

                                let kind = ExprKind::FieldAccess {
                                    name: field.name().to_string(),
                                    operand: spread_value,
                                };
                                let expr = self.push_expr_kind(kind, field.ty(), stmts);
                                value_fields.push((field.name().to_string(), expr));
                                initialized_fields.insert(field.name());
                            }
                        }
                    }
                }

                // Reversed -> Ordered
                value_fields.reverse();

                let kind = ExprKind::StructValue(value_fields);
                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Minus(a) => {
                let a = self.build_expr(a, program, stmts);
                let kind = ExprKind::Minus(a);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Add(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Add(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Sub(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Sub(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Mul(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Mul(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Div(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Div(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Eq(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Eq(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Ne(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Ne(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Lt(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Lt(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Gt(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Gt(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Le(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Le(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Ge(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Ge(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::And(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::And(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Or(a, b) => {
                let a = self.build_expr(a, program, stmts);
                let b = self.build_expr(b, program, stmts);
                let kind = ExprKind::Or(a, b);

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Var(name) => {
                let kind = ExprKind::Var(Var::new(name, expr_ty));
                self.push_expr_kind(kind, expr_ty, stmts)
            }
            &syntax::ExprKind::IndexAccess(operand, index) => {
                let expected_ty = expr_ty;
                let operand = self.build_expr(operand, program, stmts);

                // expected_ty might be an auto generated union type.
                program.add_decl_type(expected_ty);

                match operand.ty().bottom_ty() {
                    Type::Tuple(_) => {
                        self.push_expr_alloc(Expr::tuple_index_access(operand, index), stmts)
                    }
                    Type::Union(operand_member_types) => {
                        let ctx = self.builder_context();
                        let union_tag =
                            self.push_expr_alloc(Expr::union_tag(self.tcx, operand), stmts);
                        let union_member_value = build_union_member_value(
                            &ctx,
                            operand,
                            operand_member_types,
                            union_tag,
                            expected_ty,
                            |_, member_value| {
                                // Pre: member_value is a tuple value which have the element.
                                let access = self
                                    .expr_arena
                                    .alloc(Expr::tuple_index_access(member_value, index));
                                self.promote_to(access, expected_ty, stmts)
                            },
                        );
                        self.push_expr(union_member_value, stmts)
                    }
                    ty => unreachable!("unsupported type: {}", ty),
                }
            }
            syntax::ExprKind::FieldAccess(operand, name) => {
                let expected_ty = expr_ty;
                let operand = self.build_expr(operand, program, stmts);

                // expected_ty might be an auto generated union type.
                program.add_decl_type(expected_ty);

                match operand.ty().bottom_ty() {
                    Type::Struct(_) => {
                        self.push_expr_alloc(Expr::struct_field_access(operand, name), stmts)
                    }
                    Type::Union(operand_member_types) => {
                        let ctx = self.builder_context();
                        let union_tag =
                            self.push_expr_alloc(Expr::union_tag(self.tcx, operand), stmts);

                        let union_member_value = build_union_member_value(
                            &ctx,
                            operand,
                            operand_member_types,
                            union_tag,
                            expected_ty,
                            |_, member_value| {
                                // Pre: member_value is a struct value which have the field.
                                let access = self
                                    .expr_arena
                                    .alloc(Expr::struct_field_access(member_value, name));
                                self.promote_to(access, expected_ty, stmts)
                            },
                        );
                        self.push_expr(union_member_value, stmts)
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
                        let arg_expr = self.build_expr(arg, program, stmts);
                        self.promote_to(arg_expr, arg_ty, stmts)
                    })
                    .collect();
                let kind = ExprKind::Call {
                    name: call_expr.name().to_string(),
                    cc: CallingConvention::Std(sig),
                    args,
                };

                self.push_expr_kind(kind, expr_ty, stmts)
            }
            syntax::ExprKind::Puts(args) => {
                // Generates `printf(...)` code for each `puts(...)`.
                // It generates many `printf(...)` but these consequence `printf(...)`s will be
                // combined in the optimization phase.
                let mut it = args.iter().peekable();

                while let Some(arg) = it.next() {
                    let a = self.build_expr(arg, program, stmts);
                    self.build_print_expr(a, false, program, stmts);

                    // separated by a space
                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(" "), stmts);
                    }
                }

                self._build_printf(FormatSpec::Str("\n"), stmts)
            }
            syntax::ExprKind::Case {
                head,
                arms,
                else_body,
            } => {
                let t = self.next_temp_var(expr.ty().unwrap());
                let t_head = self.build_expr(head, program, stmts);

                // Construct "if-else" statement from each branches.
                let mut branches = arms
                    .iter()
                    .map(|arm| {
                        // Build an condition and variable declarations from the pattern
                        let mut branch_stmts = vec![];

                        let condition = self.build_pattern(
                            t_head,
                            arm.pattern(),
                            program,
                            stmts,
                            &mut branch_stmts,
                        );

                        let mut ret = None;
                        for stmt in arm.body() {
                            ret = self.build_stmt(stmt, program, &mut branch_stmts);
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
                        ret = self.build_stmt(stmt, program, &mut branch_stmts);
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
        &mut self,
        operand: &'a Expr<'a, 'tcx>,
        expected_ty: &'tcx Type<'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        let operand_ty = operand.ty().bottom_ty();
        let expected_ty = expected_ty.bottom_ty();

        match (operand_ty, expected_ty) {
            (Type::Union(operand_member_types), Type::Union(expected_member_types)) => {
                if operand_member_types == expected_member_types {
                    return operand;
                }

                let ctx = self.builder_context();
                let union_tag = self.push_expr_alloc(Expr::union_tag(self.tcx, operand), stmts);

                let union_member_value = build_union_member_value(
                    &ctx,
                    operand,
                    operand_member_types,
                    union_tag,
                    expected_ty,
                    |tag, member_value| {
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
                        let member_value = self
                            .expr_arena
                            .alloc(Expr::union_member_access(operand, tag, member_ty));
                        let member_value = self.promote_to(member_value, expected_member_ty, stmts);

                        let union_value = self.push_expr_alloc(
                            Expr::union_value(self.tcx, member_value, expected_tag, expected_ty),
                            stmts,
                        );

                        &*union_value
                    },
                );
                self.push_expr(union_member_value, stmts)
            }
            (operand_ty, Type::Union(member_types)) => {
                for (tag, mty) in member_types.iter().enumerate() {
                    if operand_ty.is_assignable_to(mty) {
                        let value = self.promote_to(operand, mty, stmts);
                        let kind = ExprKind::UnionValue { value, tag };
                        return self.push_expr_kind(kind, expected_ty, stmts);
                    }
                }
                unreachable!(
                    "no matched member type for union {} with operand: {}",
                    expected_ty, operand_ty
                );
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
                        let expr = self.push_expr_alloc(expr, stmts);
                        let value = self.promote_to(expr, f.ty(), stmts);

                        (f.name().to_string(), value)
                    })
                    .collect();

                self.push_expr_kind(ExprKind::StructValue(promoted_fields), expected_ty, stmts)
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
                        let expr = self.push_expr_alloc(expr, stmts);
                        self.promote_to(expr, fty, stmts)
                    })
                    .collect();
                self.push_expr_kind(ExprKind::Tuple(m), expected_ty, stmts)
            }
            _ => operand,
        }
    }

    fn build_print_expr(
        &mut self,
        arg: &'a Expr<'a, 'tcx>,
        quote_string: bool,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        match arg.ty() {
            Type::Int64
            | Type::NativeInt
            | Type::Boolean
            | Type::LiteralInt64(_)
            | Type::LiteralBoolean(_) => self._build_printf(FormatSpec::Value(arg), stmts),
            Type::String | Type::LiteralString(_) => {
                if quote_string {
                    self._build_printf(FormatSpec::Quoted(arg), stmts)
                } else {
                    self._build_printf(FormatSpec::Value(arg), stmts)
                }
            }
            Type::Tuple(fs) => {
                let mut it = fs.iter().enumerate().peekable();

                self._build_printf(FormatSpec::Str("("), stmts);
                while let Some((i, sub_ty)) = it.next() {
                    let kind = ExprKind::IndexAccess {
                        operand: arg,
                        index: i,
                    };

                    let ir_expr = self.push_expr_kind(kind, sub_ty, stmts);
                    self.build_print_expr(ir_expr, true, program, stmts);

                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(", "), stmts);
                    }
                }
                self._build_printf(FormatSpec::Str(")"), stmts)
            }
            Type::Struct(struct_ty) => {
                if let Some(name) = struct_ty.name() {
                    self._build_printf(FormatSpec::Value(self.const_string(name)), stmts);
                    self._build_printf(FormatSpec::Str(" "), stmts);
                }

                // print typed fields
                let mut it = struct_ty.fields().iter().peekable();
                let empty = it.peek().is_none();

                self._build_printf(FormatSpec::Str("{"), stmts);
                if !empty {
                    self._build_printf(FormatSpec::Str(" "), stmts);
                }

                while let Some(f) = it.next() {
                    self._build_printf(FormatSpec::Value(self.const_string(f.name())), stmts);
                    self._build_printf(FormatSpec::Str(": "), stmts);

                    let kind = ExprKind::FieldAccess {
                        operand: arg,
                        name: f.name().to_string(),
                    };

                    let ir_expr = self.push_expr_kind(kind, f.ty(), stmts);
                    self.build_print_expr(ir_expr, true, program, stmts);

                    if it.peek().is_some() {
                        self._build_printf(FormatSpec::Str(", "), stmts);
                    }
                }

                if !empty {
                    self._build_printf(FormatSpec::Str(" "), stmts);
                }
                self._build_printf(FormatSpec::Str("}"), stmts)
            }
            Type::Union(member_types) => {
                // For union type values, the appropriate value is output by
                // branching on the condition of the tag of the value.
                let t = self.next_temp_var(self.tcx.int64());
                let get_union_tag = self.push_expr_alloc(Expr::union_tag(self.tcx, arg), stmts);

                // generates branches
                let mut branches = vec![];
                for (tag, member_ty) in member_types.iter().enumerate() {
                    let mut branch_stmts = vec![];

                    // check union tag
                    let value = self.expr_arena.alloc(Expr::usize(self.tcx, tag));
                    let cond = self
                        .expr_arena
                        .alloc(Expr::eq(self.tcx, get_union_tag, value));

                    // print union member
                    let kind = ExprKind::UnionMemberAccess { operand: arg, tag };
                    let member =
                        self.push_expr_alloc(Expr::new(kind, member_ty), &mut branch_stmts);

                    let ret =
                        self.build_print_expr(member, quote_string, program, &mut branch_stmts);
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
        &mut self,
        format_spec: FormatSpec<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> &'a Expr<'a, 'tcx> {
        self.push_expr_alloc(Expr::printf(self.tcx, vec![format_spec]), stmts)
    }

    // Returns `None` for no condition.
    fn build_pattern(
        &mut self,
        target_expr: &'a Expr<'a, 'tcx>,
        pat: &'nd syntax::Pattern<'nd, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        outer_stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) -> Option<&'a Expr<'a, 'tcx>> {
        // zero-sized type is always matched with a value.
        if pat.expect_ty().is_zero_sized() {
            return None;
        }

        match pat.kind() {
            &PatternKind::Integer(n) => {
                let value = self.expr_arena.alloc(Expr::int64(self.tcx, n));
                let eq = Expr::eq(self.tcx, target_expr, value);
                Some(self.expr_arena.alloc(eq))
            }
            PatternKind::Boolean(b) => {
                let expr = if *b {
                    target_expr
                } else {
                    self.expr_arena.alloc(Expr::not(self.tcx, target_expr))
                };
                Some(expr)
            }
            PatternKind::String(s) => {
                // Compare the value of head expression and pattern string with
                // POSIX `strcmp` function.
                let value = self.const_string(s);
                let kind = ExprKind::Call {
                    name: "strcmp".to_string(),
                    cc: CallingConvention::C,
                    args: vec![target_expr, value],
                };
                let strcmp = self.expr_arena.alloc(Expr::new(kind, self.tcx.int64()));

                let zero = self.native_int(0);
                let eq = Expr::eq(self.tcx, strcmp, zero);

                Some(self.expr_arena.alloc(eq))
            }
            &PatternKind::Range { lo, hi, end } => {
                let lo = self.expr_arena.alloc(Expr::int64(self.tcx, lo));
                let hi = self.expr_arena.alloc(Expr::int64(self.tcx, hi));

                let lhs = Expr::ge(self.tcx, target_expr, lo);

                let rhs = match end {
                    syntax::RangeEnd::Included => Expr::le(self.tcx, target_expr, hi),
                    syntax::RangeEnd::Excluded => Expr::lt(self.tcx, target_expr, hi),
                };

                let eq = Expr::and(
                    self.tcx,
                    self.expr_arena.alloc(lhs),
                    self.expr_arena.alloc(rhs),
                );

                Some(self.expr_arena.alloc(eq))
            }
            PatternKind::Tuple(sub_pats) => {
                if sub_pats.is_empty() {
                    unreachable!(
                        "Empty tuple must be zero-sized type. It should be handled above."
                    );
                }

                sub_pats.iter().enumerate().fold(None, |cond, (i, pat)| {
                    let kind = ExprKind::IndexAccess {
                        operand: target_expr,
                        index: i,
                    };
                    let operand = self.expr_arena.alloc(Expr::new(kind, pat.expect_ty()));
                    let sub_cond = self.build_pattern(operand, pat, program, outer_stmts, stmts);

                    match (cond, sub_cond) {
                        (Some(cond), Some(sub_cond)) => {
                            Some(self.expr_arena.alloc(Expr::and(self.tcx, cond, sub_cond)))
                        }
                        (Some(cond), None) => Some(cond),
                        (None, Some(sub_cond)) => Some(sub_cond),
                        (None, None) => None,
                    }
                })
            }
            PatternKind::Struct(struct_pat) => {
                if struct_pat.fields().is_empty() {
                    unreachable!(
                        "Empty struct must be zero-sized type. It should be handled above."
                    );
                }

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
                        let values = self.struct_values(struct_ty, target_expr);
                        let struct_value = self
                            .expr_arena
                            .alloc(Expr::new(ExprKind::StructValue(values), spread_ty));

                        let var_def =
                            Stmt::VarDef(VarDef::new(spread_name.to_string(), struct_value));
                        stmts.push(self.stmt_arena.alloc(var_def));
                    }
                }

                pattern_fields.iter().fold(None, |cond, pat_field| {
                    let kind = ExprKind::FieldAccess {
                        operand: target_expr,
                        name: pat_field.name().to_string(),
                    };
                    let operand = self
                        .expr_arena
                        .alloc(Expr::new(kind, pat_field.pattern().expect_ty()));
                    let sub_cond = self.build_pattern(
                        operand,
                        pat_field.pattern(),
                        program,
                        outer_stmts,
                        stmts,
                    );

                    match (cond, sub_cond) {
                        (Some(cond), Some(sub_cond)) => {
                            Some(self.expr_arena.alloc(Expr::and(self.tcx, cond, sub_cond)))
                        }
                        (Some(cond), None) => Some(cond),
                        (None, Some(sub_cond)) => Some(sub_cond),
                        (None, None) => None,
                    }
                })
            }
            PatternKind::Var(name) => {
                let value = self.promote_to(target_expr, pat.expect_ty(), stmts);
                let stmt = Stmt::VarDef(VarDef::new(name.clone(), value));
                stmts.push(self.stmt_arena.alloc(stmt));

                None
            }
            PatternKind::Or(sub_pats) => {
                assert!(sub_pats.len() >= 2);
                let bool_ty = self.tcx.boolean();

                sub_pats.iter().fold(None, |cond, sub_pat| {
                    // control flow variable
                    let cfv = self.next_control_flow_var();
                    let stmt = Stmt::tmp_var_def(cfv, self.bool(false));
                    outer_stmts.push(self.stmt_arena.alloc(stmt));

                    let mut inner_stmts = vec![];
                    let sub_cond = self.build_pattern(
                        target_expr,
                        sub_pat,
                        program,
                        outer_stmts,
                        &mut inner_stmts,
                    );

                    self.merge_var_decl_stmts(cfv, stmts, &inner_stmts);

                    let cond_and_assign = self.expr_arena.alloc(Expr::new(
                        ExprKind::CondAndAssign {
                            cond: sub_cond,
                            var: cfv,
                        },
                        bool_ty,
                    ));

                    if let Some(cond) = cond {
                        let kind = ExprKind::Or(cond, cond_and_assign);
                        Some(self.expr_arena.alloc(Expr::new(kind, bool_ty)))
                    } else {
                        Some(cond_and_assign)
                    }
                })
            }
            PatternKind::Wildcard => None,
        }
    }

    fn merge_var_decl_stmts(
        &self,
        cfv: &'a TmpVar<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
        inner_stmts: &[&'a Stmt<'a, 'tcx>],
    ) {
        for stmt in inner_stmts {
            if let Stmt::VarDef(def) = stmt {
                let v = stmts.iter().enumerate().find_map(|(i, x)| {
                    if let Stmt::VarDef(x_def) = x {
                        if x_def.name() == def.name() {
                            return Some((i, x_def.init()));
                        }
                    }
                    None
                });

                if let Some((i, else_value)) = v {
                    let cfv_expr = Expr::tmp_var(cfv);
                    let init = Expr::new(
                        ExprKind::CondValue {
                            cond: self.expr_arena.alloc(cfv_expr),
                            then_value: def.init(),
                            else_value,
                        },
                        def.init().ty(),
                    );
                    let new_var_def = Stmt::VarDef(VarDef::new(
                        def.name().to_string(),
                        self.expr_arena.alloc(init),
                    ));

                    stmts.push(self.stmt_arena.alloc(new_var_def));
                    stmts.swap_remove(i);
                } else {
                    let var_def = Stmt::VarDef(VarDef::new(def.name().to_string(), def.init()));
                    stmts.push(self.stmt_arena.alloc(var_def));
                }
            } else {
                unreachable!("stmt must be var def: {}", stmt);
            }
        }
    }

    fn _build_let_pattern(
        &mut self,
        pattern: &'nd syntax::Pattern<'nd, 'tcx>,
        init: &'a Expr<'a, 'tcx>,
        program: &mut Program<'a, 'tcx>,
        stmts: &mut Vec<&'a Stmt<'a, 'tcx>>,
    ) {
        match pattern.kind() {
            PatternKind::Var(name) => {
                program.add_decl_type(pattern.expect_ty());

                let value = self.promote_to(init, pattern.expect_ty(), stmts);
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
                    let field = self.push_expr_kind(kind, sub_pat.expect_ty(), stmts);
                    self._build_let_pattern(sub_pat, field, program, stmts)
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
                            let field =
                                self.push_expr_kind(kind, pat_field.pattern().expect_ty(), stmts);
                            self._build_let_pattern(pat_field.pattern(), field, program, stmts)
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
}

fn build_union_member_value<'a, 'tcx, F>(
    ctx: &BuilderContext<'a, 'tcx>,
    operand: &'a Expr<'a, 'tcx>,
    operand_member_types: &[&'tcx Type<'tcx>],
    operand_union_tag: &'a Expr<'a, 'tcx>,
    expected_ty: &'tcx Type<'tcx>,
    mut member_value_mapper: F,
) -> &'a Expr<'a, 'tcx>
where
    F: FnMut(usize, &'a Expr<'a, 'tcx>) -> &'a Expr<'a, 'tcx>,
{
    // condition and value conversion.
    let vs: Vec<_> = operand_member_types
        .iter()
        .enumerate()
        .map(|(tag, member_ty)| {
            let value = ctx.expr_arena.alloc(Expr::usize(ctx.tcx, tag));
            let cond = ctx
                .expr_arena
                .alloc(Expr::eq(ctx.tcx, operand_union_tag, value));

            // member access
            let member_value = ctx
                .expr_arena
                .alloc(Expr::union_member_access(operand, tag, member_ty));

            let result = member_value_mapper(tag, member_value);
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
                ctx.expr_arena.alloc(Expr::new(kind, expected_ty))
            });

    cond_value_expr
}
