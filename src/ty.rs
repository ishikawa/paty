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

    pub fn empty_anon_struct_ty(&self) -> &'tcx Type<'tcx> {
        self.anon_struct_ty(vec![])
    }

    /// Returns a struct type whose name is `name` and has no value.
    pub fn empty_struct_ty(&self, name: String) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_named(name, vec![]);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }

    pub fn anon_struct_ty(&self, fields: Vec<TypedField<'tcx>>) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_anonymous(fields);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }

    pub fn struct_ty(&self, name: String, fields: Vec<TypedField<'tcx>>) -> &'tcx Type<'tcx> {
        let struct_ty = StructTy::new_named(name, fields);
        self.type_arena.alloc(Type::Struct(struct_ty))
    }

    pub fn unit(&self) -> &'tcx Type<'tcx> {
        self.tuple_n(0)
    }

    /// Returns a tuple type whose element type is unknown but has N elements.
    pub fn tuple_n(&self, n: usize) -> &'tcx Type<'tcx> {
        let mut value_types = vec![];

        if n > 0 {
            let undetermined = &*self.type_arena.alloc(Type::Undetermined);

            for _ in 0..n {
                value_types.push(undetermined);
            }
        }

        self.tuple(&value_types)
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
            Type::Struct(struct_ty) => struct_ty.fields().iter().all(|f| f.ty().is_zero_sized()),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypedField<'tcx> {
    name: String,
    ty: &'tcx Type<'tcx>,
}

impl<'tcx> TypedField<'tcx> {
    pub fn new(name: String, ty: &'tcx Type<'tcx>) -> Self {
        Self { name, ty }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn ty(&self) -> &'tcx Type<'tcx> {
        self.ty
    }
}

impl fmt::Display for TypedField<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: ", self.name)?;
        write!(f, "{}", self.ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructTy<'tcx> {
    name: Option<String>,
    fields: Vec<TypedField<'tcx>>,
}

impl<'tcx> StructTy<'tcx> {
    pub fn new_anonymous(fields: Vec<TypedField<'tcx>>) -> Self {
        Self::new(None, fields)
    }

    pub fn new_named(name: String, fields: Vec<TypedField<'tcx>>) -> Self {
        Self::new(Some(name), fields)
    }

    pub fn new(name: Option<String>, fields: Vec<TypedField<'tcx>>) -> Self {
        if name.is_none() {
            // The order of fields must be sorted so that anonymous struct can be
            // matched by structural.
            let mut fs = fields;
            fs.sort_by(|a, b| a.name().cmp(b.name()));
            Self { name, fields: fs }
        } else {
            Self { name, fields }
        }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn fields(&self) -> &[TypedField<'tcx>] {
        self.fields.as_slice()
    }

    pub fn get_field(&self, name: &str) -> Option<&TypedField<'tcx>> {
        self.fields.iter().find(|f| f.name() == name)
    }
}

impl fmt::Display for StructTy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = self.name() {
            write!(f, "struct {} ", name)?;
        }

        let mut it = self.fields().iter().peekable();
        let empty = it.peek().is_none();

        write!(f, "{{")?;
        if !empty {
            write!(f, " ")?;
        }
        while let Some(field) = it.next() {
            write!(f, "{}", field)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        if !empty {
            write!(f, " ")?;
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

/// The signature of a function is a combination of the function name and
/// the order of the types of the function's parameters. The type of the return
/// value of the function is irrelevant to the signature.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionSignature<'tcx> {
    name: String,
    params: Vec<&'tcx Type<'tcx>>,
}

impl<'tcx> FunctionSignature<'tcx> {
    pub fn new(name: String, params: Vec<&'tcx Type<'tcx>>) -> Self {
        Self { name, params }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn params(&self) -> &[&'tcx Type<'tcx>] {
        &self.params
    }
}

impl fmt::Display for FunctionSignature<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.name.fmt(f)?;
        write!(f, "(")?;

        let mut it = self.params.iter().peekable();

        while let Some(ty) = it.next() {
            ty.fmt(f)?;
            if it.peek().is_some() {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}
