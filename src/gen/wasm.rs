//! WebAssembly backend which emits WAT (WebAssembly Text Format).
pub mod builder;

use std::fmt;

use self::builder as wasm;
use self::builder::{
    Entity, Export, ExportDesc, Import, ImportDesc, Instruction, MemArg, Module, WatBuilder,
};
use crate::ir::inst::{Expr, ExprKind, FormatSpec, Function, Program, Stmt};

use super::util::mangle_name;

/// WebAssembly has 32-bit and 64-bit architecture variants,
/// called wasm32 and wasm64. wasm32 has an ILP32 data model,
/// meaning that int, long, and pointer types are all 32-bit,
/// while the long long type is 64-bit. wasm64 has an LP64 data model,
/// meaning that long and pointer types will be 64-bit,
/// while int is 32-bit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WasmArch {
    Bits32 = 32,
    Bits64 = 64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EmitterOptions {
    pub arch: WasmArch,
    /// Supports WASI (WebAssembly System Interface) or not.
    pub wasi: bool,
}

/// The base address of the constant pool in WASM memory.
const CONSTANT_POOL_BASE: u32 = 8;

/// The name of a global variable which points to the current stack pointer.
const SP: &str = "sp";

/// The name of a global variable which points to the current base pointer.
const BP: &str = "bp";

/// Functions in prelude. You can get function id from `prelude.id()`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Prelude {
    FdWriteAll,
    FdWriteI64,
}

impl Prelude {
    pub fn id(&self) -> &str {
        match self {
            Self::FdWriteAll => "@fd_write_all",
            Self::FdWriteI64 => "@fd_write_i64",
        }
    }
}

impl fmt::Display for Prelude {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id())
    }
}

#[derive(Debug)]
pub struct Emitter {
    options: EmitterOptions,

    /// CP (constant pool pointer)
    cp: u32,
}

impl<'a, 'tcx> Emitter {
    pub fn new(options: EmitterOptions) -> Self {
        Self {
            options,
            cp: CONSTANT_POOL_BASE,
        }
    }

    pub fn emit(&mut self, program: &'a Program<'a, 'tcx>) -> String {
        let mut module = Module::new();

        // -- imports
        if self.options.wasi {
            // fd_write(fd: fd, iovs: ciovec_array) -> Result<size, errno>
            let fun_fd_write = wasm::FunctionSignature::new(
                vec![
                    Entity::named("fd", wasm::Type::I32),
                    Entity::named("iovs", wasm::Type::I32),
                    Entity::named("iovs_len", wasm::Type::I32),
                    Entity::named("nwritten", wasm::Type::I32),
                ],
                vec![wasm::Type::I32],
            );

            module.push_import(Import::new(
                "wasi_snapshot_preview1".into(),
                "fd_write".into(),
                ImportDesc::Function(Entity::named("fd_write", fun_fd_write)),
            ));
        }

        // -- exports
        module.push_export(Export::new(
            "memory".into(),
            ExportDesc::Memory(wasm::Index::Index(0)),
        ));

        // Emit functions
        for fun in program.functions() {
            self.emit_function(fun, &mut module);
        }

        // Now, the CP (constant pool address) points to the base address of
        // program stack. Write it to the BP and SP global.
        let stack_base_address =
            wasm::Global::new(true, wasm::Type::I32, vec![Instruction::i32_const(self.cp)]);
        module.push_global(Entity::named(BP, stack_base_address.clone()));
        module.push_global(Entity::named(SP, stack_base_address));

        // -- build
        let mut wat = WatBuilder::new();
        wat.emit(&Entity::named("demo.wat", module))
    }

    /// Define a prelude function if not yet present. returns
    /// the prelude enum.
    fn use_prelude(&mut self, prelude: Prelude, module: &mut Module) -> Prelude {
        let fun_id = prelude.id();

        if !module
            .functions()
            .any(|fun| fun.id().filter(|id| *id == fun_id).is_some())
        {
            self.define_prelude(prelude, module);
        }
        prelude
    }

    fn define_prelude(&mut self, prelude: Prelude, module: &mut Module) {
        let wasm_fun = match prelude {
            Prelude::FdWriteAll => self.build_prelude_fd_write_all(module),
            Prelude::FdWriteI64 => self.build_prelude_fd_write_i64(module),
        };
        module.prepend_function(Entity::named(prelude.id(), wasm_fun));
    }
    /// Defines `fd_write_all` function.
    ///
    /// ```ignore
    /// @fd_write_all(fd: i32, io_vs: i32) error
    /// ```
    fn build_prelude_fd_write_all(&mut self, _module: &mut Module) -> wasm::Function {
        // locals
        let param_fd = "fd";
        let param_io_vs = "io_vs";
        let io_vs_ptr = "tmp_io_vs";
        let n_written_ptr = "tmp_n_written";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(param_fd, wasm::Type::I32),
                Entity::named(param_io_vs, wasm::Type::I32),
            ],
            vec![wasm::Type::I32],
        ));
        wasm_fun.push_local(Entity::named(io_vs_ptr, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(n_written_ptr, wasm::Type::I32));

        self.emit_function_prologue(&mut wasm_fun);

        // local: copy io_vs array to the stack.
        wasm_fun.instructions_mut().extend([
            Instruction::i64_store(
                Instruction::local_tee(io_vs_ptr, Instruction::global_get(SP)),
                Instruction::i64_load(Instruction::local_get(param_io_vs)),
            ),
            self.build_incr_sp(8),
        ]);

        // local: n_written
        wasm_fun.instructions_mut().extend([
            Instruction::local_set(n_written_ptr, Instruction::global_get(SP)),
            self.build_incr_sp(4),
        ]);

        // begin loop
        let mut wasm_loop = wasm::LoopInstruction::with_result(wasm::Type::I32);
        {
            // call fd_write()
            wasm_loop.instructions_mut().push(Instruction::call(
                "fd_write",
                vec![
                    Instruction::local_get(param_fd),
                    Instruction::local_get(io_vs_ptr),
                    // io_vs_len - We're printing 1 string stored in an iov - so one.
                    Instruction::i32_const(1),
                    Instruction::local_get(n_written_ptr),
                ],
            ));
            // TODO: check n_written and loop until flush.
            // v = io_vs_ptr[1] - *n_written
            // continue if v != 0
            // wasm_fun.extend_instructions([
            //     Instruction::i32_sub(
            //         Instruction::i32_load_m(
            //             MemArg::with_offset(4),
            //             Instruction::local_get(io_vs_ptr),
            //         ),
            //         Instruction::i32_load(Instruction::local_get(n_written_ptr)),
            //     ),
            //     Instruction::br_if(
            //         0,
            //         Instruction::i32_ne(Instruction::nop(), Instruction::i32_const(0)),
            //     ),
            // ]);
        }
        // /end loop
        wasm_fun
            .instructions_mut()
            .push(Instruction::r#loop(wasm_loop));

        self.emit_function_epilogue(&mut wasm_fun);
        wasm_fun
    }
    /// Build a prelude function prints digits from the given integer.
    ///
    /// Input
    ///
    /// - `fd: i32` - file descriptor
    /// - `n: i64` - an integer value
    ///
    /// Output
    ///
    /// - `error: i32`
    fn build_prelude_fd_write_i64(&mut self, module: &mut Module) -> wasm::Function {
        // Defines the "0".."9" table.
        let digits = "0123456789";
        let table_ptr = Instruction::i32_const(self.cp);

        module.push_data_segment(Entity::named(
            "digits",
            wasm::DataSegment::new(
                vec![table_ptr.clone()],
                vec![wasm::StringData::String(digits.into())],
            ),
        ));
        self.cp += digits.len().align(4);

        // locals
        let param_fd = "fd";
        let param_n = "n";
        let n = "tmp_n";

        let io_vec_ptr = "tmp_io_vec_ptr";
        let n_columns = "tmp_n_columns";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(param_fd, wasm::Type::I32),
                Entity::named(param_n, wasm::Type::I64),
            ],
            vec![wasm::Type::I32],
        ));
        wasm_fun.push_local(Entity::named(n, wasm::Type::I64));
        wasm_fun.push_local(Entity::named(io_vec_ptr, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(n_columns, wasm::Type::I32));
        self.emit_function_prologue(&mut wasm_fun);

        // tmp_n = n
        wasm_fun
            .instructions_mut()
            .push(Instruction::local_set(n, Instruction::local_get(param_n)));

        // The algorithm
        // -------------
        // 1. Allocates a memory for preserving an io_vector_array.
        // 2. Allocates enough memory on the stack to print 32-bits integers.
        // 3. Writes digits in order from the lower digits, from the higher to
        //    the lower direction of the allocated memory.
        // 4. Writes `buf` and `buf_len` into (1).
        // 5. Prints io_vec_array by using `fd_write`.

        wasm_fun.instructions_mut().extend([
            // Saves the address of io_vec_array.
            Instruction::local_set(io_vec_ptr, Instruction::global_get(SP)),
            // Allocates memory for string.
            self.build_incr_sp(
                // io_vec_array + string
                (8 + i64::MIN.to_string().len()).align(4),
            ),
        ]);

        // ------
        // begin loop - until all digits printed
        let mut wasm_loop = wasm::LoopInstruction::new();

        // n_columns += 1
        wasm_loop.instructions_mut().push(Instruction::local_set(
            n_columns,
            Instruction::i32_add(Instruction::local_get(n_columns), Instruction::i32_const(1)),
        ));
        // i = tmp_n % 10
        // c: u8 = table[i]
        // *(SP - n_columns) = c
        wasm_loop.instructions_mut().push(Instruction::i32_store8(
            Instruction::i32_sub(
                Instruction::global_get(SP),
                Instruction::local_get(n_columns),
            ),
            Instruction::i32_load8_u(Instruction::i32_add(
                table_ptr,
                Instruction::i32_wrap_i64(Instruction::i64_rem_u(
                    Instruction::local_get(n),
                    Instruction::i64_const(10),
                )),
            )),
        ));

        // tmp_n = tmp_n / 10
        // continue if tmp_n != 0
        wasm_loop.instructions_mut().push(Instruction::br_if(
            0,
            Instruction::i64_ne(
                Instruction::local_tee(
                    n,
                    Instruction::i64_div_u(Instruction::local_get(n), Instruction::i64_const(10)),
                ),
                Instruction::i64_const(0),
            ),
        ));

        // end loop
        wasm_fun
            .instructions_mut()
            .push(Instruction::r#loop(wasm_loop));

        // writes `buf` and `buf_len`
        wasm_fun.instructions_mut().push(Instruction::i32_store(
            Instruction::local_get(io_vec_ptr),
            Instruction::i32_sub(
                Instruction::global_get(SP),
                Instruction::local_get(n_columns),
            ),
        ));
        wasm_fun.instructions_mut().push(Instruction::i32_store_m(
            MemArg::with_offset(4),
            Instruction::local_get(io_vec_ptr),
            Instruction::local_get(n_columns),
        ));

        // calls fd_write()
        let fd_write_all = self.use_prelude(Prelude::FdWriteAll, module);
        wasm_fun.instructions_mut().push(Instruction::call(
            fd_write_all.id(),
            vec![
                Instruction::local_get(param_fd),
                Instruction::local_get(io_vec_ptr),
            ],
        ));

        // register function
        self.emit_function_epilogue(&mut wasm_fun);
        wasm_fun
    }

    fn emit_function(&mut self, fun: &Function<'a, 'tcx>, module: &mut Module) {
        let mut wasm_fun = wasm::Function::new();

        // params
        assert!(fun.params.is_empty());

        if !fun.is_entry_point {
            self.emit_function_prologue(&mut wasm_fun);
        }

        // body
        for stmt in &fun.body {
            self.emit_stmt(stmt, &mut wasm_fun, module);
        }

        if !fun.is_entry_point {
            self.emit_function_epilogue(&mut wasm_fun);
        }

        // function name
        let mangled_name = mangle_name(&fun.signature);
        module.push_function(Entity::named(mangled_name.to_string(), wasm_fun));

        // Start function for WASI ABI (legacy)
        // https://github.com/WebAssembly/WASI/blob/main/legacy/application-abi.md
        if fun.is_entry_point {
            module.push_export(Export::new(
                "_start".into(),
                ExportDesc::Function(wasm::Index::Id(mangled_name)),
            ));
        }
    }

    fn emit_stmt(
        &mut self,
        stmt: &Stmt<'a, 'tcx>,
        wasm_fun: &mut wasm::Function,
        module: &mut Module,
    ) {
        match stmt {
            Stmt::TmpVarDef(def) => {
                assert_eq!(def.var().used(), 0);
                self.emit_expr(def.init(), wasm_fun, module);
            }
            Stmt::VarDef(_) => todo!(),
            Stmt::Cond(_) => todo!(),
            Stmt::Phi(_) => todo!(),
            Stmt::Ret(_) => {}
        }
    }

    fn emit_function_prologue(&mut self, wasm_fun: &mut wasm::Function) {
        wasm_fun.instructions_mut().extend([
            // Saves the caller's BP and update BP
            Instruction::i32_store(Instruction::global_get(SP), Instruction::global_get(BP)),
            Instruction::global_set(BP, Instruction::global_get(SP)),
            // Advances SP
            self.build_incr_sp(4),
        ]);
    }
    fn emit_function_epilogue(&mut self, wasm_fun: &mut wasm::Function) {
        // Restore the caller's FP
        wasm_fun.instructions_mut().extend([
            Instruction::global_set(SP, Instruction::global_get(BP)),
            Instruction::global_set(BP, Instruction::i32_load(Instruction::global_get(BP))),
        ]);
    }

    #[allow(unused_variables)]
    fn emit_expr(
        &mut self,
        expr: &Expr<'a, 'tcx>,
        wasm_fun: &mut wasm::Function,
        module: &mut Module,
    ) {
        match expr.kind() {
            ExprKind::Minus(_) => todo!(),
            ExprKind::Not(_) => todo!(),
            ExprKind::Add(_, _) => todo!(),
            ExprKind::Sub(_, _) => todo!(),
            ExprKind::Mul(_, _) => todo!(),
            ExprKind::Div(_, _) => todo!(),
            ExprKind::Eq(_, _) => todo!(),
            ExprKind::Ne(_, _) => todo!(),
            ExprKind::Lt(_, _) => todo!(),
            ExprKind::Le(_, _) => todo!(),
            ExprKind::Gt(_, _) => todo!(),
            ExprKind::Ge(_, _) => todo!(),
            ExprKind::And(_, _) => todo!(),
            ExprKind::Or(_, _) => todo!(),
            ExprKind::Call { name, cc, args } => todo!(),
            ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => todo!(),
            ExprKind::CondAndAssign { cond, var } => todo!(),
            ExprKind::Printf(args) => {
                for arg in args {
                    // file_descriptor - 1 for stdout
                    wasm_fun.instructions_mut().push(Instruction::i32_const(1));

                    // io_vs - The pointer to the iov array
                    match arg {
                        FormatSpec::Value(value) => {
                            self.emit_expr(value, wasm_fun, module);
                        }
                        FormatSpec::Quoted(_) => todo!(),
                        FormatSpec::Str(s) => {
                            self.emit_string(s, wasm_fun, module);
                        }
                    }

                    // call WASI `fd_write` function.
                    let fd_write_all = self.use_prelude(Prelude::FdWriteAll, module);
                    wasm_fun
                        .instructions_mut()
                        .push(Instruction::call(fd_write_all.id(), vec![]));

                    // ----- DEBUG
                    // let fd_write_i64 = self.use_prelude(Prelude::FdWriteI64, module);
                    // let tmp = wasm_fun.push_tmp(wasm::Type::I64);

                    // wasm_fun.instructions_mut().push(Instruction::local_set(
                    //     tmp.clone(),
                    //     Instruction::i64_extend_i32_s(
                    //         Instruction::nop(), // result - fd_write_all
                    //     ),
                    // ));
                    // wasm_fun.instructions_mut().push(Instruction::call(
                    //     fd_write_i64.id(),
                    //     vec![Instruction::i32_const(2), Instruction::local_get(tmp)],
                    // ));
                    // /DEBUG

                    wasm_fun.instructions_mut().push(Instruction::drop());
                }
            }
            ExprKind::Int64(_) => todo!(),
            ExprKind::Bool(_) => todo!(),
            ExprKind::Str(s) => {
                self.emit_string(s, wasm_fun, module);
            }
            ExprKind::Tuple(_) => todo!(),
            ExprKind::StructValue(_) => todo!(),
            ExprKind::IndexAccess { operand, index } => todo!(),
            ExprKind::FieldAccess { operand, name } => todo!(),
            ExprKind::TmpVar(_) => todo!(),
            ExprKind::Var(_) => todo!(),
            ExprKind::UnionTag(_) => todo!(),
            ExprKind::UnionMemberAccess { operand, tag } => todo!(),
            ExprKind::UnionValue { value, tag } => todo!(),
        }
    }

    /// Emit the specified string `s` into a WASM function body. It also add a new data
    /// segment which holds a constant string as `ciovec` structure in WASI.
    ///
    /// ```ignore
    /// WASM stack:
    ///   IN: []
    ///   OUT: [ciovec location (u32)]
    /// ```
    fn emit_string(&mut self, s: &str, wasm_fun: &mut wasm::Function, module: &mut Module) {
        // Write a string into the constant pool.
        // The data structure is same as [`ciovec`](https://github.com/WebAssembly/WASI/blob/main/phases/snapshot/docs.md#-ciovec-record) in WASI.
        //
        // +--------+-------------+
        // | ciovec | string data |
        // +--------+-------------+
        //
        // ciovec: Record
        // - 0: `buf` - `ConstPointer<u8>`
        // - 4: `buf_len` - `size`
        const CIOVEC_LEN: usize = 8;
        let mut ciovec: [u8; CIOVEC_LEN] = [0; CIOVEC_LEN];
        // `buf` - The address of the constant string.
        let str_base = self.cp + CIOVEC_LEN.align(4);
        // `buf_len` - The length of the buffer to be written.
        let str_len = u32::try_from(s.len()).unwrap();

        ciovec[..4].clone_from_slice(&str_base.to_le_bytes());
        ciovec[4..].clone_from_slice(&str_len.to_le_bytes());

        let data_loc = Instruction::i32_const(self.cp);
        let data_segment = wasm::DataSegment::new(
            vec![data_loc.clone()],
            vec![
                wasm::StringData::Bytes(Box::new(ciovec)),
                wasm::StringData::String(s.to_string()),
            ],
        );
        module.push_data_segment(Entity::new(data_segment));

        self.cp = (str_base + str_len).align(4);

        // The pointer to the iov array
        wasm_fun.instructions_mut().push(data_loc);
    }
}

impl Emitter {
    fn build_incr_sp(&self, n: u32) -> Instruction {
        Instruction::global_set(
            SP,
            Instruction::i32_add(Instruction::global_get(SP), Instruction::i32_const(n)),
        )
    }
    #[allow(unused)]
    fn build_decr_sp(&mut self, n: u32) -> Instruction {
        Instruction::global_set(
            SP,
            Instruction::i32_sub(Instruction::global_get(SP), Instruction::i32_const(n)),
        )
    }
}

trait Address {
    /// Increase an integer operand to a next address aligned to
    /// to the `alignment`.
    fn align(self, alignment: u32) -> u32;
}

impl Address for u32 {
    #[inline]
    fn align(self, alignment: u32) -> u32 {
        // https://stackoverflow.com/a/45213645/14957276
        ((self + (alignment - 1)) / alignment) * alignment
    }
}

impl Address for usize {
    #[inline]
    fn align(self, alignment: u32) -> u32 {
        u32::try_from(self).unwrap().align(alignment)
    }
}

#[cfg(test)]
mod tests_utils {
    use super::*;

    #[test]
    fn address_align() {
        assert_eq!(0_u32.align(4), 0);
        assert_eq!(1_u32.align(4), 4);
        assert_eq!(4_u32.align(4), 4);
        assert_eq!(29_u32.align(4), 32);
    }
}
