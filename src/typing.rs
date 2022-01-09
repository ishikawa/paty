#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type {
    /// 64bit integer
    Int64,
    /// `true` or `false`
    Boolean,
}
