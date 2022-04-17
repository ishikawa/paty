//! WebAssembly backend which emits WAT (WebAssembly Text Format).
mod builder;

use crate::ir::inst::Program;

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

#[derive(Debug)]
pub struct Emitter {
    //options: EmitterOptions,
}

impl Emitter {
    pub fn new(_options: EmitterOptions) -> Self {
        Self {}
    }

    pub fn emit<'a, 'tcx>(&mut self, _program: &'a Program<'a, 'tcx>) -> String {
        let module = builder::Module::new(Some("demo.wat".into()));
        let mut wat = builder::WatBuilder::new();

        wat.emit(&module)
    }
}
