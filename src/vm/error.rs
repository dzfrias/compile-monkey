use thiserror::Error;

use crate::{frontend::ast::InfixOp, object::Type};

pub type Result<T> = std::result::Result<T, RuntimeError>;

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("invalid types: {lhs} and {rhs} with operation \"{op}\"")]
    InvalidTypes { lhs: Type, rhs: Type, op: InfixOp },
    #[error("stack overflow")]
    StackOverflow,
    #[error("integer overflow")]
    IntegerOverflow,
}
