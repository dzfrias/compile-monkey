use thiserror::Error;

use crate::object::Type;

pub type Result<T> = std::result::Result<T, RuntimeError>;

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error("expected type: {expected}, got: {got}")]
    ExpectedType { expected: Type, got: Type },
    #[error("stack overflow")]
    StackOverflow,
    #[error("integer overflow")]
    IntegerOverflow,
}
