//! WebAssembly
//! https://webassembly.github.io/spec/core/intro/introduction.html

/// WebAssembly programs are organized into modules,
/// which are the unit of deployment, loading, and compilation.
///
/// https://webassembly.github.io/spec/core/syntax/modules.html
#[derive(Debug)]
pub struct Module {
    name: Option<String>,
    imports: Vec<Import>,
}

impl Module {
    pub fn new(name: Option<String>, imports: Vec<Import>) -> Self {
        Self { name, imports }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn imports(&self) -> impl ExactSizeIterator<Item = &Import> {
        self.imports.iter()
    }
}

/// The `imports` component of a module defines a set of imports that are
/// required for instantiation.
#[derive(Debug)]
pub struct Import {
    /// A `module` name.
    module: String,
    /// A name for an entity within that module.
    name: String,
    /// Each import is specified by a descriptor with a respective type that
    /// a definition provided during instantiation is required to match.
    desc: ImportDesc,
}

impl Import {
    pub fn new(module: String, name: String, desc: ImportDesc) -> Self {
        Self { module, name, desc }
    }

    pub fn module(&self) -> &str {
        self.module.as_str()
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn desc(&self) -> &ImportDesc {
        &self.desc
    }
}

#[derive(Debug)]
pub enum ImportDesc {
    Function(FunctionSignature),
}

#[derive(Debug)]
pub struct FunctionSignature {
    name: Option<String>,
    params: Vec<FunctionParam>,
    results: Vec<Type>,
}

impl FunctionSignature {
    pub fn new(name: Option<String>, params: Vec<FunctionParam>, results: Vec<Type>) -> Self {
        Self {
            name,
            params,
            results,
        }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn params(&self) -> impl ExactSizeIterator<Item = &FunctionParam> {
        self.params.iter()
    }

    pub fn results(&self) -> impl ExactSizeIterator<Item = &Type> {
        self.results.iter()
    }
}

#[derive(Debug)]
pub struct FunctionParam {
    name: Option<String>,
    ty: Type,
}

impl FunctionParam {
    pub fn new(name: Option<String>, ty: Type) -> Self {
        Self { name, ty }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }
}
/// Various entities in WebAssembly are classified by types.
/// Types are checked during validation, instantiation, and
/// possibly execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    // Number Types
    // The types  and  classify 32 and 64 bit integers, respectively.
    // Integers are not inherently signed or unsigned, their interpretation is
    // determined by individual operations.
    I32,
    #[allow(dead_code)]
    I64,
    // The types  and  classify 32 and 64 bit floating-point data, respectively.
    // They correspond to the respective binary floating-point representations,
    // also known as single and double precision, as defined by
    // the IEEE 754-2019 standard
    #[allow(dead_code)]
    F32,
    #[allow(dead_code)]
    F64,
}

pub trait Visitor {
    fn enter_module(&mut self, module: &Module);
    fn exit_module(&mut self, module: &Module);

    fn enter_import(&mut self, import: &Import);
    fn exit_import(&mut self, import: &Import);
}

fn walk(visitor: &mut dyn Visitor, module: &Module) {
    visitor.enter_module(module);
    for import in module.imports() {
        visitor.enter_import(import);
        visitor.exit_import(import);
    }
    visitor.exit_module(module);
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

    fn emit_id(&mut self, id: &str) {
        self.buffer.push('$');
        self.buffer.push_str(id);
    }
    fn emit_str(&mut self, s: &str) {
        self.buffer.push('"');
        for c in s.escape_default() {
            self.buffer.push(c);
        }
        self.buffer.push('"');
    }
    fn emit_type(&mut self, ty: &Type) {
        self.buffer.push_str(match ty {
            Type::I32 => "i32",
            Type::I64 => "i64",
            Type::F32 => "f32",
            Type::F64 => "f64",
        });
    }
    fn emit_function_signature(&mut self, fun: &FunctionSignature) {
        self.buffer.push('(');
        self.buffer.push_str("func");

        if let Some(name) = fun.name() {
            self.buffer.push(' ');
            self.emit_id(name);
        }
        self.buffer.push(' ');

        for param in fun.params() {
            self.buffer.push('(');
            self.buffer.push_str("param");
            self.buffer.push(' ');
            if let Some(name) = param.name() {
                self.emit_id(name);
                self.buffer.push(' ');
            }
            self.emit_type(param.ty());
            self.buffer.push(')');
        }

        for ty in fun.results() {
            self.buffer.push('(');
            self.buffer.push_str("result");
            self.buffer.push(' ');
            self.emit_type(ty);
            self.buffer.push(')');
        }

        self.buffer.push(')');
    }
}

impl Visitor for WatBuilder {
    fn enter_module(&mut self, module: &Module) {
        self.buffer.push('(');
        self.buffer.push_str("module");

        if let Some(name) = module.name() {
            self.buffer.push(' ');
            self.emit_id(name);
        }
    }
    fn exit_module(&mut self, _module: &Module) {
        self.buffer.push(')');
    }

    fn enter_import(&mut self, import: &Import) {
        self.buffer.push('(');
        self.buffer.push_str("import");

        self.buffer.push(' ');
        self.emit_str(import.module());
        self.buffer.push(' ');
        self.emit_str(import.name());
        self.buffer.push(' ');

        match import.desc() {
            ImportDesc::Function(fun) => self.emit_function_signature(fun),
        }
    }
    fn exit_import(&mut self, _import: &Import) {
        self.buffer.push(')');
    }
}
