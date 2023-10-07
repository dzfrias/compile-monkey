use thiserror::Error;

use crate::{
    frontend::ast::{InfixOp, PrefixOp},
    object::Type,
};

pub type Result<T> = std::result::Result<T, RuntimeError>;

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("invalid types: {lhs} and {rhs} with operation \"{op}\"")]
    InvalidTypes { lhs: Type, rhs: Type, op: InfixOp },
    #[error("invalid type: {expr} with operation \"{op}\"")]
    InvalidType { expr: Type, op: PrefixOp },
    #[error("stack overflow")]
    StackOverflow,
    #[error("integer overflow")]
    IntegerOverflow,
    #[error("cannot index {lhs} with {rhs}")]
    IndexNotSupported { lhs: Type, rhs: Type },
    #[error("array index out of range")]
    IndexOutOfRange,
    #[error("uncallable type: {0}")]
    UncallableType(Type),
    #[error("wrong number of arguments provided, got: {got}, expected: {expected}")]
    WrongArgs { got: u32, expected: u32 },
    #[error("wrong argument type provided, got: {got}, expected: {want}")]
    WrongArgType { got: Type, want: Type },
}
