//! Based on usefulness algorithm in Rust:
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/usefulness.rs
//! - https://github.com/rust-lang/rust/blob/d331cb710f0/compiler/rustc_mir_build/src/thir/pattern/deconstruct_pat.rs
use std::cell::Cell;

/// A value can be decomposed into a constructor applied to some fields. This struct represents
/// those fields, generalized to allow patterns in each field. See also `Constructor`.
///
/// This is constructed for a constructor using [`Fields::wildcards()`]. The idea is that
/// [`Fields::wildcards()`] constructs a list of fields where all entries are wildcards, and then
/// given a pattern we fill some of the fields with its subpatterns.
/// In the following example `Fields::wildcards` returns `[_, _, _, _]`. Then in
/// `extract_pattern_arguments` we fill some of the entries, and the result is
/// `[Some(0), _, _, _]`.
/// ```rust
/// let x: [Option<u8>; 4] = foo();
/// match x {
///     [Some(0), ..] => {}
/// }
/// ```
///
/// Note that the number of fields of a constructor may not match the fields declared in the
/// original struct/variant. This happens if a private or `non_exhaustive` field is uninhabited,
/// because the code mustn't observe that it is uninhabited. In that case that field is not
/// included in `fields`. For that reason, when you have a `mir::Field` you must use
/// `index_with_declared_idx`.
#[derive(Debug, Clone, Copy)]
pub struct Fields<'p> {
    fields: &'p [DeconstructedPat<'p>],
}

/// A value can be decomposed into a constructor applied to some fields. This struct represents
/// the constructor. See also `Fields`.
///
/// `pat_constructor` retrieves the constructor corresponding to a pattern.
/// `specialize_constructor` returns the list of fields corresponding to a pattern, given a
/// constructor. `Constructor::apply` reconstructs the pattern from a pair of `Constructor` and
/// `Fields`.
#[derive(Clone, Debug, PartialEq)]
pub enum Constructor {
    /// Wildcard pattern.
    Wildcard,
}

/// Values and patterns can be represented as a constructor applied to some fields. This represents
/// a pattern in this form.
/// This also keeps track of whether the pattern has been found reachable during analysis. For this
/// reason we should be careful not to clone patterns for which we care about that. Use
/// `clone_and_forget_reachability` if you're sure.
#[derive(Debug)]
pub struct DeconstructedPat<'p> {
    ctor: Constructor,
    fields: Fields<'p>,
    reachable: Cell<bool>,
}

/// The arm of a match expression.
#[derive(Clone, Copy)]
pub struct MatchArm<'p> {
    /// The pattern must have been lowered through `check_match::MatchVisitor::lower_pattern`.
    pub pat: &'p DeconstructedPat<'p>,
    pub has_guard: bool,
}

/// Indicates whether or not a given arm is reachable.
#[derive(Clone, Debug)]
pub enum Reachability {
    /// The arm is reachable.
    Reachable,
    /// The arm is unreachable.
    Unreachable,
}

/// The output of checking a match for exhaustiveness and arm reachability.
pub struct UsefulnessReport<'p> {
    /// For each arm of the input, whether that arm is reachable after the arms above it.
    pub arm_usefulness: Vec<(MatchArm<'p>, Reachability)>,
    /// If the match is exhaustive, this is empty. If not, this contains witnesses for the lack of
    /// exhaustiveness.
    pub non_exhaustiveness_witnesses: Vec<DeconstructedPat<'p>>,
}

/// The entrypoint for the usefulness algorithm. Computes whether a match is exhaustive and which
/// of its arms are reachable.
///
/// Note: the input patterns must have been lowered through
/// `check_match::MatchVisitor::lower_pattern`.
pub fn compute_match_usefulness<'p, 'tcx>(arms: &[MatchArm<'p>]) -> UsefulnessReport<'p> {
    todo!();
}
