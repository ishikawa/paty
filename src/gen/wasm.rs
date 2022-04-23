//! WebAssembly backend which emits WAT (WebAssembly Text Format).
pub mod builder;

use self::builder as wasm;
use self::builder::{
    Entity, Export, ExportDesc, Import, ImportDesc, Instruction, Module, WatBuilder,
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
                    Entity::named("fd".into(), wasm::Type::I32),
                    Entity::named("iovs".into(), wasm::Type::I32),
                    Entity::named("iovs_len".into(), wasm::Type::I32),
                    Entity::named("nwritten".into(), wasm::Type::I32),
                ],
                vec![wasm::Type::I32],
            );

            module.push_import(Import::new(
                "wasi_snapshot_preview1".into(),
                "fd_write".into(),
                ImportDesc::Function(Entity::named("fd_write".into(), fun_fd_write)),
            ));
        }

        self.define_prelude(&mut module);

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
        module.push_global(Entity::named(BP.into(), stack_base_address.clone()));
        module.push_global(Entity::named(SP.into(), stack_base_address.clone()));

        // -- build
        let mut wat = WatBuilder::new();
        wat.emit(&Entity::named("demo.wat".into(), module))
    }

    /// The prelude; a standard module; is defined by default.
    fn define_prelude(&mut self, module: &mut Module) {
        self.define_prelude_fd_write_all(module);
    }
    /// Defines `fd_write_all` function.
    ///
    /// ```ignore
    /// fd_write_all($fd: i32, io_vs: i32, n_written) error
    /// ```
    fn define_prelude_fd_write_all(&mut self, module: &mut Module) {
        // param names
        let local_fd = "fd";
        let local_io_vs = "io_vs";
        let local_n_written = "n_written";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(local_fd.into(), wasm::Type::I32),
                Entity::named(local_io_vs.into(), wasm::Type::I32),
                Entity::named(local_n_written.into(), wasm::Type::I32),
            ],
            vec![wasm::Type::I32],
        ));

        self.emit_function_prologue(&mut wasm_fun);

        // call fd_write()
        wasm_fun.push_instruction(Instruction::call(
            "fd_write".into(),
            vec![
                Instruction::local_get(local_fd.into()),
                Instruction::local_get(local_io_vs.into()),
                // io_vs_len - We're printing 1 string stored in an iov - so one.
                Instruction::i32_const(1),
                Instruction::local_get(local_n_written.into()),
            ],
        ));

        self.emit_function_epilogue(&mut wasm_fun);

        module.push_function(Entity::named("@fd_write_all".into(), wasm_fun));
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
        // Saves the caller's BP and update BP
        wasm_fun.push_instruction(Instruction::i32_store(
            Instruction::global_get(SP.into()),
            Instruction::global_get(BP.into()),
        ));
        wasm_fun.push_instruction(Instruction::global_set(
            BP.into(),
            Instruction::global_get(SP.into()),
        ));
        // Advances SP
        wasm_fun.push_instruction(Instruction::global_set(
            SP.into(),
            Instruction::i32_add(
                Instruction::global_get(SP.into()),
                Instruction::i32_const(4),
            ),
        ));
    }
    fn emit_function_epilogue(&mut self, wasm_fun: &mut wasm::Function) {
        // Restore the caller's FP
        wasm_fun.push_instruction(Instruction::global_set(
            SP.into(),
            Instruction::global_get(BP.into()),
        ));
        wasm_fun.push_instruction(Instruction::global_set(
            BP.into(),
            Instruction::i32_load(Instruction::global_get(BP.into())),
        ));
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
                    wasm_fun.push_instruction(Instruction::i32_const(1));

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

                    // n_written - A place in memory to store the number of bytes written.
                    // we don't check error so doesn't advance the SP.
                    wasm_fun.push_instruction(Instruction::global_get(SP.into()));

                    // call WASI `fd_write` function.
                    wasm_fun.push_instruction(Instruction::call("@fd_write_all".into(), vec![]));
                    wasm_fun.push_instruction(Instruction::drop());
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
        wasm_fun.push_instruction(data_loc);
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
