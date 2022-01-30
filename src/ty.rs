use std::hash::{Hash, Hasher};
use std::{cell::Cell, fmt};
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

    pub fn undetermined(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::Undetermined)
    }

    pub fn tuple(&self, value_types: &[&'tcx Type<'tcx>]) -> &'tcx Type<'tcx> {
        self.type_arena
            .alloc(Type::Tuple(value_types.iter().copied().collect()))
    }

    /// Returns a tuple type whose element type is unknown but has N elements.
    pub fn tuple_n(&self, n: usize) -> &'tcx Type<'tcx> {
        let mut value_types = vec![];
        let undetermined = &*self.type_arena.alloc(Type::Undetermined);

        for _ in 0..n {
            value_types.push(undetermined);
        }

        self.tuple(&value_types)
    }

    /// Returns a struct type whose name is `name` and has no value.
    pub fn named_struct(&self, name: &str) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new(name, vec![]);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }

    pub fn native_int(&self) -> &'tcx Type<'tcx> {
        self.type_arena.alloc(Type::NativeInt)
    }
}

#[derive(Debug, Clone, Eq)]
pub enum Type<'tcx> {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
    /// string
    String,
    /// tuple
    Tuple(Vec<&'tcx Type<'tcx>>),
    /// struct
    Struct(StructTy<'tcx>),

    /// Type is specified by name and should be resolved in the later phase
    Named(NamedTy<'tcx>),

    /// Type is not specified and should be inferred in the later phase.
    Undetermined,

    // C types for internal uses
    /// int
    NativeInt,
}

impl<'tcx> Type<'tcx> {
    pub fn bottom_ty(&'tcx self) -> &'tcx Type<'tcx> {
        if let Type::Named(named_ty) = self {
            if let Some(ty) = named_ty.ty() {
                ty.bottom_ty()
            } else {
                self
            }
        } else {
            self
        }
    }

    /// Returns `true` if the type is zero-sized.
    pub fn is_zero_sized(&self) -> bool {
        match self {
            Type::Int64 | Type::Boolean | Type::String | Type::NativeInt => false,
            Type::Tuple(fs) => fs.is_empty() || fs.iter().all(|x| x.is_zero_sized()),
            Type::Struct(struct_ty) => {
                struct_ty.is_empty() || struct_ty.fields().all(|(_, fty)| fty.is_zero_sized())
            }
            Type::Named(named_ty) => {
                if let Some(ty) = named_ty.ty() {
                    ty.is_zero_sized()
                } else {
                    true
                }
            }
            Type::Undetermined => true,
        }
    }
}

impl PartialEq for Type<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Tuple(l0), Self::Tuple(r0)) => l0 == r0,
            (Self::Struct(l0), Self::Struct(r0)) => l0 == r0,
            (Self::Named(named_ty1), Self::Named(named_ty2)) => {
                named_ty1.name() == named_ty2.name() || named_ty1.ty() == named_ty2.ty()
            }
            (Self::Named(named_ty1), ty2) => {
                if let Some(ty1) = named_ty1.ty() {
                    ty1 == ty2
                } else {
                    false
                }
            }
            (ty1, Self::Named(named_ty2)) => {
                if let Some(ty2) = named_ty2.ty() {
                    ty1 == ty2
                } else {
                    false
                }
            }
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl Hash for Type<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Type::Tuple(fs) => fs.hash(state),
            Type::Struct(struct_ty) => struct_ty.hash(state),
            Type::Named(named_ty) => {
                if let Some(ty) = named_ty.ty() {
                    ty.hash(state)
                } else {
                    named_ty.name().hash(state)
                }
            }
            Type::Int64 | Type::Boolean | Type::String | Type::Undetermined | Type::NativeInt => {
                core::mem::discriminant(self).hash(state)
            }
        }
    }
}

impl fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int64 => write!(f, "int64"),
            Type::Boolean => write!(f, "boolean"),
            Type::String => write!(f, "string"),
            Type::NativeInt => write!(f, "int"),
            Type::Named(named_ty) => named_ty.fmt(f),
            Type::Undetermined => write!(f, "_"),
            Type::Tuple(value_types) => {
                let mut it = value_types.iter().peekable();
                write!(f, "(")?;
                while let Some(ty) = it.next() {
                    write!(f, "{}", ty)?;
                    if it.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Type::Struct(struct_ty) => struct_ty.fmt(f),
        }
    }
}

pub type StructTyField<'tcx> = (String, &'tcx Type<'tcx>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTy<'tcx> {
    name: String,
    fields: Vec<StructTyField<'tcx>>,
}

impl<'tcx> StructTy<'tcx> {
    pub fn new(name: &str, fields: Vec<StructTyField<'tcx>>) -> Self {
        Self {
            name: name.to_string(),
            fields,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn is_empty(&self) -> bool {
        self.fields.is_empty()
    }

    pub fn fields(&self) -> impl ExactSizeIterator<Item = &StructTyField<'tcx>> {
        self.fields.iter()
    }

    pub fn get_field(&self, name: &str) -> Option<&StructTyField<'tcx>> {
        self.fields.iter().find(|f| f.0 == name)
    }
}

impl fmt::Display for StructTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "struct {} ", self.name())?;

        let mut it = self.fields().peekable();
        write!(f, "{{")?;
        while let Some((fname, ty)) = it.next() {
            write!(f, "{}: ", fname)?;
            write!(f, "{}", ty)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedTy<'tcx> {
    name: String,
    ty: Cell<Option<&'tcx Type<'tcx>>>,
}

impl<'tcx> NamedTy<'tcx> {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            ty: Cell::new(None),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> Option<&'tcx Type<'tcx>> {
        self.ty.get()
    }

    pub fn expect_ty(&self) -> &'tcx Type<'tcx> {
        self.ty().unwrap_or_else(|| {
            panic!(
                "Semantic analyzer couldn't assign type for named type `{}`",
                self.name
            );
        })
    }

    pub fn assign_ty(&self, ty: &'tcx Type<'tcx>) {
        self.ty.set(Some(ty))
    }
}

impl fmt::Display for NamedTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)
    }
}
