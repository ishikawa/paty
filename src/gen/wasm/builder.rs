//! WebAssembly
//! https://webassembly.github.io/spec/core/intro/introduction.html

/// WebAssembly programs are organized into modules,
/// which are the unit of deployment, loading, and compilation.
///
/// https://webassembly.github.io/spec/core/syntax/modules.html
#[derive(Debug)]
pub struct Module {
    name: Option<String>,
}

impl Module {
    pub fn new(name: Option<String>) -> Self {
        Self { name }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
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
    fn visit_module(&mut self, module: &Module) {
        self.buffer.push('(');
        self.buffer.push_str("module");

        if let Some(name) = module.name() {
            self.buffer.push(' ');
            self.buffer.push('$');
            self.buffer.push_str(name);
        }

        self.buffer.push(')');
    }
}
