use thiserror::Error;

pub type Result<T> = std::result::Result<T, CompilerError>;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error("unbound variable: {name}")]
    UnboundVariable { name: String },
}
