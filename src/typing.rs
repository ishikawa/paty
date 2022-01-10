use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Int64 => write!(f, "int64"),
            Type::Boolean => write!(f, "boolean"),
        }
    }
}
