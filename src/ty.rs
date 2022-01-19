use std::fmt;
use typed_arena::Arena;

#[derive(Clone, Copy)]
pub struct TypeContext<'tcx> {
    pub type_arena: &'tcx Arena<Type<'tcx>>,
}

impl<'tcx> TypeContext<'tcx> {
    pub fn new(type_arena: &'tcx Arena<Type<'tcx>>) -> Self {
        Self { type_arena }
    }

    pub fn int64(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Int64)
    }

    pub fn boolean(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Boolean)
    }

    pub fn string(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::String)
    }

    pub fn tuple(&self, value_types: &[&'tcx Type<'tcx>]) -> &'tcx Type<'tcx> {
        self.type_arena
            .alloc(Type::Tuple(value_types.iter().copied().collect()))
    }

    pub fn native_int(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::NativeInt)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type<'tcx> {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
    /// string
    String,
    /// tuple
    Tuple(Vec<&'tcx Type<'tcx>>),

    // C types for internal uses
    /// int
    NativeInt,
}

impl fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int64 => write!(f, "int64"),
            Type::Boolean => write!(f, "boolean"),
            Type::String => write!(f, "string"),
            Type::NativeInt => write!(f, "int"),
            Type::Tuple(_) => todo!(),
        }
    }
}
