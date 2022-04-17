//! WebAssembly
//! https://webassembly.github.io/spec/core/intro/introduction.html

/// WebAssembly programs are organized into modules,
/// which are the unit of deployment, loading, and compilation.
///
/// https://webassembly.github.io/spec/core/syntax/modules.html
#[derive(Debug)]
pub struct Module {}

impl Module {
    pub fn new() -> Self {
        Self {}
    }
}

pub trait Visitor {
    fn visit_module(&mut self, module: &Module);
}

fn walk(visitor: &mut dyn Visitor, module: &Module) {
    visitor.visit_module(module);
}

#[derive(Debug)]
pub struct WatBuilder {
    buffer: String,
}

impl WatBuilder {
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
        }
    }

    pub fn emit(&mut self, module: &Module) -> String {
        self.buffer.clear();

        walk(self, module);
        std::mem::take(&mut self.buffer)
    }
}

impl Visitor for WatBuilder {
    fn visit_module(&mut self, _module: &Module) {
        self.buffer.push('(');
        self.buffer.push_str("module");
        self.buffer.push(')');
    }
}
