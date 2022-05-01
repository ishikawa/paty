//! WebAssembly backend which emits WAT (WebAssembly Text Format).
pub mod builder;

use std::collections::HashMap;
use std::fmt;

use self::builder as wasm;
use self::builder::{
    Entity, Export, ExportDesc, Import, ImportDesc, Instruction, MemArg, Module, WatBuilder,
};
use crate::ir::inst::{Expr, ExprKind, FormatSpec, Function, Program, Stmt};
use crate::ty::Type;

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
    // Functions
    FdWriteAll,
    FdWriteI64,
    FdWriteU32,
    FdDebugU8,
    AbsI64,
}

impl Prelude {
    pub fn id(&self) -> &str {
        match self {
            Self::FdWriteAll => "@fd_write_all",
            Self::FdWriteI64 => "@fd_write_i64",
            Self::FdWriteU32 => "@fd_write_u32",
            Self::FdDebugU8 => "@fd_debug_u8",
            Self::AbsI64 => "@abs_i64",
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

    /// string constant => (ciovec_ptr, string_ptr)
    strings: HashMap<String, (u32, u32)>,
}

impl<'a, 'tcx> Emitter {
    pub fn new(options: EmitterOptions) -> Self {
        Self {
            options,
            cp: CONSTANT_POOL_BASE,
            strings: HashMap::new(),
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
                    Entity::named("io_vs", wasm::Type::I32),
                    Entity::named("io_vs_len", wasm::Type::I32),
                    Entity::named("n_written", wasm::Type::I32),
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

    /// Defines a string constant in the given module and returns its address that
    /// points to ciovec. If you want to take an address of string bytes, it is
    /// `address + 8`.
    ///
    /// The data structure is same as [`ciovec`](https://github.com/WebAssembly/WASI/blob/main/phases/snapshot/docs.md#-ciovec-record) in WASI.
    ///
    /// ```ignore
    /// +--------+-------------+
    /// | ciovec | string data |
    /// +--------+-------------+
    /// ```
    ///
    /// ciovec: Record
    /// - 0: `buf` - `ConstPointer<u8>`
    /// - 4: `buf_len` - `size`
    fn define_string_constant(&mut self, s: &str, module: &mut Module) -> (u32, u32) {
        if let Some(address) = self.strings.get(s) {
            return *address;
        }

        const CIOVEC_LEN: usize = 8;
        let io_vec_ptr = self.cp;
        let mut ciovec: [u8; CIOVEC_LEN] = [0; CIOVEC_LEN];
        // `buf` - The address of the constant string.
        let str_base = io_vec_ptr + CIOVEC_LEN.align(4);
        // `buf_len` - The length of the buffer to be written.
        let str_len = u32::try_from(s.len()).unwrap();

        ciovec[..4].clone_from_slice(&str_base.to_le_bytes());
        ciovec[4..].clone_from_slice(&str_len.to_le_bytes());

        let data_segment = wasm::DataSegment::new(
            vec![Instruction::i32_const(io_vec_ptr)],
            vec![
                wasm::StringData::Bytes(Box::new(ciovec)),
                wasm::StringData::String(s.to_string()),
            ],
        );
        module.push_data_segment(Entity::new(data_segment));

        self.cp = (str_base + str_len).align(4);
        self.strings.insert(s.into(), (io_vec_ptr, str_base));

        (io_vec_ptr, str_base)
    }

    /// Defines a prelude function if not yet present. returns
    /// the prelude enum.
    fn use_prelude<'prelude>(
        &mut self,
        module: &mut Module,
        prelude: &'prelude Prelude,
    ) -> &'prelude str {
        let fun_id = prelude.id();

        if !module
            .functions()
            .any(|fun| fun.id().filter(|id| *id == fun_id).is_some())
        {
            self.define_prelude(prelude, module);
        }

        prelude.id()
    }

    fn define_prelude(&mut self, prelude: &Prelude, module: &mut Module) {
        let wasm_fun = match prelude {
            Prelude::FdWriteAll => self.build_prelude_fd_write_all(module),
            Prelude::FdWriteI64 => self.build_prelude_fd_write_i64(module),
            Prelude::FdWriteU32 => self.build_prelude_fd_write_u32(module),
            Prelude::FdDebugU8 => self.build_prelude_fd_debug_u8(module),
            Prelude::AbsI64 => self.build_prelude_abs_i64(module),
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

        wasm_fun
            .body_mut()
            // local: copy io_vs array to the stack.
            .i64_store(
                Instruction::local_tee(io_vs_ptr, Instruction::global_get(SP)),
                Instruction::i64_load(Instruction::local_get(param_io_vs)),
            )
            .push(self.build_advance_sp(8))
            // local: n_written
            .local_set(n_written_ptr, Instruction::global_get(SP))
            .push(self.build_advance_sp(4));

        // begin loop
        let mut wasm_loop = wasm::LoopInstruction::with_result(wasm::Type::I32);
        {
            // call fd_write()
            wasm_loop.body_mut().call(
                "fd_write",
                vec![
                    Instruction::local_get(param_fd),
                    Instruction::local_get(io_vs_ptr),
                    // io_vs_len - We're printing 1 string stored in an iov - so one.
                    Instruction::i32_const(1),
                    Instruction::local_get(n_written_ptr),
                ],
            );

            //  check n_written and loop until entire input is written.

            let n_written = wasm_fun.push_tmp(wasm::Type::I32);
            let n_left = wasm_fun.push_tmp(wasm::Type::I32);

            wasm_loop
                .body_mut()
                // n_written = *n_written_ptr
                .local_set(
                    n_written.clone(),
                    Instruction::i32_load(Instruction::local_get(n_written_ptr)),
                )
                // n_left = io_vs_ptr[1] - n_written
                .local_set(
                    n_left.clone(),
                    Instruction::i32_sub(
                        Instruction::i32_load_m(
                            MemArg::with_offset(4),
                            Instruction::local_get(io_vs_ptr),
                        ),
                        Instruction::local_get(n_written.clone()),
                    ),
                )
                // io_vs_ptr[0] += n_written
                .i32_store(
                    Instruction::local_get(io_vs_ptr),
                    Instruction::i32_add(
                        Instruction::i32_load(Instruction::local_get(io_vs_ptr)),
                        Instruction::local_get(n_written),
                    ),
                )
                // io_vs_ptr[1] = n_left
                .i32_store_m(
                    MemArg::with_offset(4),
                    Instruction::local_get(io_vs_ptr),
                    Instruction::local_get(n_left.clone()),
                )
                // continue if n_left != 0
                .br_if(
                    0,
                    Instruction::i32_ne(Instruction::local_get(n_left), Instruction::i32_const(0)),
                );
        }
        // /end loop
        wasm_fun.body_mut().push(Instruction::r#loop(wasm_loop));

        self.emit_function_epilogue(&mut wasm_fun);
        wasm_fun
    }
    /// Build a prelude function prints digits from the given integer.
    ///
    /// Input
    ///
    /// - `fd: i32` - file descriptor
    /// - `n: u32` - an integer value
    ///
    /// Output
    ///
    /// - `error: i32`
    fn build_prelude_fd_write_u32(&mut self, module: &mut Module) -> wasm::Function {
        // Defines the "0".."9" table.
        let (_, table_ptr) = self.define_string_constant("0123456789", module);

        // locals
        let param_fd = "fd";
        let param_n = "n";
        let n = "tmp_n";

        let io_vec_ptr = "tmp_io_vec_ptr";
        let n_columns = "tmp_n_columns";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(param_fd, wasm::Type::I32),
                Entity::named(param_n, wasm::Type::I32),
            ],
            vec![wasm::Type::I32],
        ));

        let tmp32 = wasm_fun.push_tmp(wasm::Type::I32);

        wasm_fun.push_local(Entity::named(n, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(io_vec_ptr, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(n_columns, wasm::Type::I32));

        self.emit_function_prologue(&mut wasm_fun);

        // tmp_n = n
        wasm_fun
            .body_mut()
            .local_set(n, Instruction::local_get(param_n));

        // The algorithm
        // -------------
        // 1. Allocates a memory for preserving an io_vector_array.
        // 2. Allocates enough memory on the stack to print 32-bits integers.
        // 3. Writes digits in order from the lower digits, from the higher to
        //    the lower direction of the allocated memory.
        // 4. Writes `buf` and `buf_len` into (1).
        // 5. Prints io_vec_array by using `fd_write`.
        wasm_fun
            .body_mut()
            // Saves the address of io_vec_array.
            .local_set(io_vec_ptr, Instruction::global_get(SP))
            // Allocates memory for string.
            .push(self.build_advance_sp(
                // io_vec_array + string
                (8 + u32::MAX.to_string().len()).align(4),
            ));

        // ------
        // begin loop - until all digits printed
        let mut wasm_loop = wasm::LoopInstruction::new();

        wasm_loop
            .body_mut()
            // n_columns += 1
            .local_set(
                n_columns,
                Instruction::i32_add(Instruction::local_get(n_columns), Instruction::i32_const(1)),
            )
            // c: u8 = table[tmp_n % 10]
            .local_set(
                tmp32.clone(),
                Instruction::i32_load8_u(Instruction::i32_add(
                    Instruction::i32_const(table_ptr),
                    Instruction::i32_rem_u(Instruction::local_get(n), Instruction::i32_const(10)),
                )),
            )
            // *(SP - n_columns) = c
            .i32_store8(
                Instruction::i32_sub(
                    Instruction::global_get(SP),
                    Instruction::local_get(n_columns),
                ),
                Instruction::local_get(tmp32),
            )
            // tmp_n = tmp_n / 10
            .local_tee(
                n,
                Instruction::i32_div_u(Instruction::local_get(n), Instruction::i32_const(10)),
            )
            // continue if tmp_n != 0
            .br_if(
                0,
                Instruction::i32_ne(Instruction::nop(), Instruction::i32_const(0)),
            );

        // end loop
        wasm_fun.body_mut().push(Instruction::r#loop(wasm_loop));

        // writes `buf` and `buf_len`
        wasm_fun
            .body_mut()
            .i32_store(
                Instruction::local_get(io_vec_ptr),
                Instruction::i32_sub(
                    Instruction::global_get(SP),
                    Instruction::local_get(n_columns),
                ),
            )
            .i32_store_m(
                MemArg::with_offset(4),
                Instruction::local_get(io_vec_ptr),
                Instruction::local_get(n_columns),
            );

        // calls fd_write()
        let fd_write_all = self.use_prelude(module, &Prelude::FdWriteAll);
        wasm_fun.body_mut().call(
            fd_write_all,
            vec![
                Instruction::local_get(param_fd),
                Instruction::local_get(io_vec_ptr),
            ],
        );

        // register function
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
        let (_, table_ptr) = self.define_string_constant("0123456789", module);

        // locals
        let param_fd = "fd";
        let param_n = "n";

        let n = "tmp_n";
        let io_vec_ptr = "io_vec_ptr";
        let n_columns = "n_columns";
        let is_negative = "is_negative";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(param_fd, wasm::Type::I32),
                Entity::named(param_n, wasm::Type::I64),
            ],
            vec![wasm::Type::I32],
        ));

        let tmp32 = wasm_fun.push_tmp(wasm::Type::I32);

        wasm_fun.push_local(Entity::named(n, wasm::Type::I64));
        wasm_fun.push_local(Entity::named(io_vec_ptr, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(n_columns, wasm::Type::I32));
        wasm_fun.push_local(Entity::named(is_negative, wasm::Type::I32));

        self.emit_function_prologue(&mut wasm_fun);

        let abs_i64 = self.use_prelude(module, &Prelude::AbsI64);

        wasm_fun
            .body_mut()
            .local_get(param_n)
            // tmp_n = abs(n)
            .call(abs_i64, vec![])
            .local_set_(n)
            // is_negative = n != tmp_n
            .local_set(
                is_negative,
                Instruction::i64_ne(Instruction::local_get(param_n), Instruction::local_get(n)),
            );

        // The algorithm
        // -------------
        // 1. Allocates a memory for preserving an io_vector_array.
        // 2. Allocates enough memory on the stack to print 32-bits integers.
        // 3. Writes digits in order from the lower digits, from the higher to
        //    the lower direction of the allocated memory.
        // 4. Writes `buf` and `buf_len` into (1).
        // 5. Prints io_vec_array by using `fd_write`.
        wasm_fun
            .body_mut()
            // Saves the address of io_vec_array.
            .local_set(io_vec_ptr, Instruction::global_get(SP))
            // Allocates memory for string.
            .push(self.build_advance_sp(
                // io_vec_array + string
                (8 + i64::MIN.to_string().len()).align(4),
            ));

        // ------
        // begin loop - until all digits printed
        let mut wasm_loop = wasm::LoopInstruction::new();

        wasm_loop
            .body_mut()
            // n_columns += 1
            .local_set(
                n_columns,
                Instruction::i32_add(Instruction::local_get(n_columns), Instruction::i32_const(1)),
            )
            // c: u8 = table[tmp_n % 10]
            .local_set(
                tmp32.clone(),
                Instruction::i32_load8_u(Instruction::i32_add(
                    Instruction::i32_const(table_ptr),
                    Instruction::i32_wrap_i64(Instruction::i64_rem_s(
                        Instruction::local_get(n),
                        Instruction::i64_const(10),
                    )),
                )),
            )
            // *(SP - n_columns) = c
            .i32_store8(
                Instruction::i32_sub(
                    Instruction::global_get(SP),
                    Instruction::local_get(n_columns),
                ),
                Instruction::local_get(tmp32),
            )
            // tmp_n = tmp_n / 10
            .local_tee(
                n,
                Instruction::i64_div_s(Instruction::local_get(n), Instruction::i64_const(10)),
            )
            // continue if tmp_n != 0
            .br_if(
                0,
                Instruction::i64_ne(Instruction::nop(), Instruction::i64_const(0)),
            );

        // end loop
        wasm_fun.body_mut().r#loop(wasm_loop);

        // minus sign "-"?
        let mut wasm_if = wasm::IfInstruction::new();

        wasm_if
            .then_body_mut()
            // n_columns += 1
            .local_set(
                n_columns,
                Instruction::i32_add(Instruction::local_get(n_columns), Instruction::i32_const(1)),
            )
            // *(SP - n_columns) = '-'
            .i32_store8(
                Instruction::i32_sub(
                    Instruction::global_get(SP),
                    Instruction::local_get(n_columns),
                ),
                Instruction::i32_const('-' as u32),
            );

        wasm_fun.body_mut().local_get(is_negative).r#if(wasm_if);

        // writes `buf` and `buf_len`
        wasm_fun
            .body_mut()
            .i32_store(
                Instruction::local_get(io_vec_ptr),
                Instruction::i32_sub(
                    Instruction::global_get(SP),
                    Instruction::local_get(n_columns),
                ),
            )
            .i32_store_m(
                MemArg::with_offset(4),
                Instruction::local_get(io_vec_ptr),
                Instruction::local_get(n_columns),
            );

        // calls fd_write()
        let fd_write_all = self.use_prelude(module, &Prelude::FdWriteAll);
        wasm_fun.body_mut().call(
            fd_write_all,
            vec![
                Instruction::local_get(param_fd),
                Instruction::local_get(io_vec_ptr),
            ],
        );

        // register function
        self.emit_function_epilogue(&mut wasm_fun);
        wasm_fun
    }
    /// Build a prelude function prints an u8 integer as printable ASCII character.
    ///
    /// Input
    ///
    /// - `fd: i32` - file descriptor
    /// - `c: u8` - u8 integer
    ///
    /// Output
    ///
    /// - `error: i32`
    fn build_prelude_fd_debug_u8(&mut self, module: &mut Module) -> wasm::Function {
        // locals
        let param_fd = "fd";
        let param_c = "c";
        let io_vec_ptr = "io_vec_ptr";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![
                Entity::named(param_fd, wasm::Type::I32),
                Entity::named(param_c, wasm::Type::I32),
            ],
            vec![wasm::Type::I32],
        ));
        wasm_fun.push_local(Entity::named(io_vec_ptr, wasm::Type::I32));
        self.emit_function_prologue(&mut wasm_fun);

        // writes `buf` and `buf_len`
        wasm_fun
            .body_mut()
            // io_vec_ptr = SP
            .local_set(io_vec_ptr, Instruction::global_get(SP))
            // SP += align(len(io_vec) + len(string))
            .push(self.build_advance_sp((8 + 1_u32).align(4)))
            // string
            .i32_store8_m(
                MemArg::with_offset(8),
                Instruction::local_get(io_vec_ptr),
                Instruction::i32_add(
                    // "!" the first printable ASCII character
                    Instruction::i32_const(33),
                    Instruction::local_get(param_c),
                ),
            )
            // io_vec - buf
            .i32_store(
                Instruction::local_get(io_vec_ptr),
                Instruction::i32_add(
                    Instruction::local_get(io_vec_ptr),
                    Instruction::i32_const(8),
                ),
            )
            // io_vec - buf len
            .i32_store_m(
                MemArg::with_offset(4),
                Instruction::local_get(io_vec_ptr),
                Instruction::i32_const(1),
            );

        // calls fd_write()
        let fd_write_all = self.use_prelude(module, &Prelude::FdWriteAll);
        wasm_fun.body_mut().call(
            fd_write_all,
            vec![
                Instruction::local_get(param_fd),
                Instruction::local_get(io_vec_ptr),
            ],
        );

        self.emit_function_epilogue(&mut wasm_fun);
        wasm_fun
    }
    /// Build a prelude function that computes the integer absolute value.
    ///
    /// Input
    ///
    /// - `value: i64` - input value
    ///
    /// Output
    ///
    /// - `value: i64`
    fn build_prelude_abs_i64(&mut self, _module: &mut Module) -> wasm::Function {
        // locals
        let param_value = "value";
        let local_mask = "mask";

        let mut wasm_fun = wasm::Function::with_signature(wasm::FunctionSignature::new(
            vec![Entity::named(param_value, wasm::Type::I64)],
            vec![wasm::Type::I64],
        ));
        wasm_fun.push_local(Entity::named(local_mask, wasm::Type::I64));

        // No stack used.
        //self.emit_function_prologue(&mut wasm_fun);

        // Since negative numbers are stored in 2's complement form, to get
        // the absolute value of a negative number we have to toggle bits of
        // the number and add 1 to the result.

        wasm_fun
            .body_mut()
            // (1) Set the mask as right shift of integer by 63 (for 64 bits integer).
            //
            //    mask = n >> 31
            .local_tee(
                local_mask,
                Instruction::i64_shr_s(
                    Instruction::local_get(param_value),
                    Instruction::i64_const(63),
                ),
            )
            // (2) Add the mask to the given number.
            //
            //    v = mask + n
            .i64_add(Instruction::nop(), Instruction::local_get(param_value))
            // (3) XOR of mask +n and mask gives the absolute value.
            //
            //    v = v ^ mask
            .i64_xor(Instruction::nop(), Instruction::local_get(local_mask));

        //self.emit_function_epilogue(&mut wasm_fun);
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
        {
            let mut body = wasm::Instructions::new();

            for stmt in &fun.body {
                self.emit_stmt(stmt, &mut wasm_fun, &mut body, module);
            }

            wasm_fun.body_mut().extend(body.into_iter());
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
        body: &mut wasm::Instructions,
        module: &mut Module,
    ) {
        match stmt {
            Stmt::TmpVarDef(def) => {
                self.emit_expr(def.init(), wasm_fun, body, module);
                // unused temporary result
                assert_eq!(def.var().used(), 0);
                body.drop();
            }
            Stmt::VarDef(var_def) => {
                let wasm_ty = wasm_type(var_def.init().ty());

                wasm_fun.push_local(Entity::named(var_def.name(), wasm_ty));
                self.emit_expr(var_def.init(), wasm_fun, body, module);
                body.local_set_(var_def.name());
            }
            Stmt::Cond(cond) => {
                // The outer block wraps child branches. WASM runtime has built-in
                // value stack, so we don't need to allocate temporary variables.
                let mut outer_block = if cond.var.used() > 0 {
                    let retty = wasm_type(cond.var.ty());
                    wasm::BlockInstruction::with_result(retty)
                } else {
                    wasm::BlockInstruction::new()
                };
                outer_block.update_label("outer".into());

                for branch in &cond.branches {
                    // An inner block has no return value.
                    let mut inner_block = wasm::BlockInstruction::new();

                    // break the branch if condition doesn't met.
                    if let Some(condition) = branch.condition {
                        self.emit_expr(condition, wasm_fun, inner_block.body_mut(), module);
                        inner_block.body_mut().i32_eqz_().br_if_(0);
                    }

                    for stmt in &branch.body {
                        self.emit_stmt(stmt, wasm_fun, inner_block.body_mut(), module);
                    }
                    // break the outer block.
                    inner_block.body_mut().br(1);

                    outer_block.body_mut().block(inner_block);
                }

                body.block(outer_block);
            }
            Stmt::Phi(_) => todo!(),
            Stmt::Ret(_) => {}
        }
    }

    #[allow(unused_variables)]
    fn emit_expr(
        &mut self,
        expr: &Expr<'a, 'tcx>,
        wasm_fun: &mut wasm::Function,
        body: &mut wasm::Instructions,
        module: &mut Module,
    ) {
        match expr.kind() {
            ExprKind::Minus(operand) => {
                body.i64_const(0);
                self.emit_expr(operand, wasm_fun, body, module);
                body.i64_sub_();
            }
            ExprKind::Not(operand) => {
                // XOR truth table
                // ^^^^^^^^^^^^^^^
                // | Input | Output  |
                // |-------|---------|
                // | A | B | A xor B |
                // | 0 | 0 | 0       |
                // | 0 | 1 | 1       |
                // | 1 | 0 | 1       |
                // | 1 | 1 | 0       |
                body.i32_const(1);
                self.emit_expr(operand, wasm_fun, body, module);
                body.i32_xor_();
            }
            ExprKind::Add(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_add_();
            }
            ExprKind::Sub(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_sub_();
            }
            ExprKind::Mul(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_mul_();
            }
            ExprKind::Div(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_div_s_();
            }
            ExprKind::Eq(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_eq_();
            }
            ExprKind::Ne(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_ne_();
            }
            ExprKind::Lt(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_lt_s_();
            }
            ExprKind::Le(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_le_s_();
            }
            ExprKind::Gt(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_gt_s_();
            }
            ExprKind::Ge(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i64_ge_s_();
            }
            ExprKind::And(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i32_and_();
            }
            ExprKind::Or(lhs, rhs) => {
                self.emit_expr(lhs, wasm_fun, body, module);
                self.emit_expr(rhs, wasm_fun, body, module);
                body.i32_or_();
            }
            ExprKind::Call { name, cc, args } => todo!(),
            ExprKind::CondValue {
                cond,
                then_value,
                else_value,
            } => todo!(),
            ExprKind::CondAndAssign { cond, var } => todo!(),
            ExprKind::Printf(args) => {
                let mut args = args.iter().peekable();

                while let Some(arg) = args.next() {
                    // file_descriptor - 1 for stdout
                    body.i32_const(1);

                    // io_vs - The pointer to the iov array
                    let value_ty = match arg {
                        FormatSpec::Value(value) => {
                            self.emit_expr(value, wasm_fun, body, module);
                            value.ty()
                        }
                        FormatSpec::Quoted(_) => todo!(),
                        FormatSpec::Str(s) => {
                            body.push(self.build_const_string(s, module));
                            &Type::String
                        }
                    };

                    let fd_write_i64 = self.use_prelude(module, &Prelude::FdWriteI64);
                    let fd_write_all = self.use_prelude(module, &Prelude::FdWriteAll);

                    match value_ty {
                        Type::Int64 | Type::LiteralInt64(_) | Type::NativeInt => {
                            body.call(fd_write_i64, vec![]);
                        }
                        Type::Boolean | Type::LiteralBoolean(_) => {
                            // v == 0 ? "false" : "true"
                            let tmp32 = wasm_fun.push_tmp(wasm::Type::I32);
                            body.local_set_(tmp32.clone())
                                .select(
                                    self.build_const_string("true", module),
                                    self.build_const_string("false", module),
                                    Instruction::local_get(tmp32),
                                )
                                .call(fd_write_all, vec![]);
                        }
                        Type::String | Type::LiteralString(_) => {
                            body.call(fd_write_all, vec![]);
                        }
                        Type::Tuple(_) => todo!(),
                        Type::Struct(_) => todo!(),
                        Type::Union(_) => todo!(),
                        Type::Named(_) => todo!(),
                        Type::Undetermined => todo!(),
                    }

                    if args.peek().is_some() {
                        // Drop intermediate results.
                        // TODO: return n_written?
                        body.drop();
                    }
                }
            }
            &ExprKind::Int64(n) => {
                body.i64_const(n as u64);
            }
            &ExprKind::Bool(b) => {
                body.i32_const(u32::try_from(b).unwrap());
            }
            ExprKind::Str(s) => {
                body.push(self.build_const_string(s, module));
            }
            ExprKind::Tuple(_) => todo!(),
            ExprKind::StructValue(_) => todo!(),
            ExprKind::IndexAccess { operand, index } => todo!(),
            ExprKind::FieldAccess { operand, name } => todo!(),
            ExprKind::TmpVar(_) => todo!(),
            ExprKind::Var(var) => {
                body.local_get(var.name());
            }
            ExprKind::UnionTag(_) => todo!(),
            ExprKind::UnionMemberAccess { operand, tag } => todo!(),
            ExprKind::UnionValue { value, tag } => todo!(),
        }
    }

    fn emit_function_prologue(&mut self, wasm_fun: &mut wasm::Function) {
        wasm_fun
            .body_mut()
            // Saves the caller's BP and update BP
            .i32_store(Instruction::global_get(SP), Instruction::global_get(BP))
            .global_set(BP, Instruction::global_get(SP))
            // Advances SP
            .push(self.build_advance_sp(4));
    }
    fn emit_function_epilogue(&mut self, wasm_fun: &mut wasm::Function) {
        wasm_fun
            .body_mut()
            // Restore the caller's FP
            .global_set(SP, Instruction::global_get(BP))
            .global_set(BP, Instruction::i32_load(Instruction::global_get(BP)));
    }

    /// Build an instruction that points to cio_vec_ptr of the specified string `s`.
    /// It also add a new data segment which holds a constant string as `ciovec`
    /// structure in WASI.
    ///
    /// ```ignore
    /// WASM stack:
    ///   IN: []
    ///   OUT: [ciovec location (u32)]
    /// ```
    fn build_const_string(&mut self, s: &str, module: &mut Module) -> Instruction {
        let (cio_vec_ptr, _) = self.define_string_constant(s, module);
        Instruction::i32_const(cio_vec_ptr)
    }

    fn build_advance_sp(&self, n: u32) -> Instruction {
        Instruction::global_set(
            SP,
            Instruction::i32_add(Instruction::global_get(SP), Instruction::i32_const(n)),
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

fn wasm_type(ty: &Type) -> wasm::Type {
    match ty {
        // All integral types are 64 bits integer.
        Type::Int64 | Type::LiteralInt64(_) | Type::NativeInt => wasm::Type::I64,
        // Boolean type in WASM is 32 bits integer 0 or 1.
        Type::Boolean | Type::LiteralBoolean(_) => wasm::Type::I32,
        // Memory location (io_vec_ptr)
        Type::String | Type::LiteralString(_) => wasm::Type::I32,
        Type::Tuple(_) => todo!(),
        Type::Struct(_) => todo!(),
        Type::Union(_) => todo!(),
        Type::Named(_) => todo!(),
        Type::Undetermined => todo!(),
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
