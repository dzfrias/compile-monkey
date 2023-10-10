#![allow(dead_code)]

mod builtins;
mod env;

use crate::opcode::Instructions;
use std::{collections::HashMap, fmt, hash::Hash};

pub(crate) use builtins::*;
pub use env::Env;

pub const TRUE: Object = Object::Bool(true);
pub const FALSE: Object = Object::Bool(false);
pub const NULL: Object = Object::Null;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Object {
    Int(i64),
    Bool(bool),
    String(String),
    Array(Vec<Object>),
    HashMap(HashMap<Object, Object>),
    Null,
    ReturnVal(Box<Object>),
    Function(Function),
    Builtin(Builtin),
    Closure(Closure),
}

impl Object {
    pub fn monkey_type(&self) -> Type {
        match self {
            Self::Int(_) => Type::INT,
            Self::Bool(_) => Type::BOOL,
            Self::String(_) => Type::STRING,
            Self::Array(_) => Type::ARRAY,
            Self::HashMap(_) => Type::HASHMAP,
            Self::Null => Type::NULL,
            Self::Function { .. } => Type::FUNCTION,
            Self::Closure(_) => Type::FUNCTION,
            Self::Builtin { .. } => Type::BUILTIN,
            Self::ReturnVal(val) => val.monkey_type(),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            Object::Int(i) => *i > 0,
            Object::Bool(b) => *b,
            Object::String(s) => !s.is_empty(),
            Object::Array(arr) => !arr.is_empty(),
            Object::HashMap(hashmap) => !hashmap.is_empty(),
            _ => false,
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(i) => write!(f, "{}", i),
            Self::Bool(b) => write!(f, "{}", b),
            Self::ReturnVal(obj) => write!(f, "{}", *obj),
            Self::Null => write!(f, "null"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Function(_) => write!(f, "func"),
            Self::Closure(_) => write!(f, "func"),
            Self::Builtin { .. } => write!(f, "[builtin function]"),
            Self::Array(arr) => {
                let joined = arr
                    .iter()
                    .map(|elem| elem.to_string() + ", ")
                    .collect::<String>();
                write!(
                    f,
                    "[{}]",
                    joined
                        .strip_suffix(", ")
                        .expect("Should always have trailing ', '")
                )
            }
            Self::HashMap(hashmap) => {
                let pairs = hashmap
                    .iter()
                    .map(|(key, val)| key.to_string() + ": " + &val.to_string())
                    .collect::<Vec<String>>();
                write!(f, "{{{}}}", pairs.join(", "))
            }
        }
    }
}

impl Hash for Object {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Int(i) => i.hash(state),
            Self::Bool(b) => b.hash(state),
            Self::String(s) => s.hash(state),
            _ => "".hash(state),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Function {
    pub instrs: Instructions,
    pub num_locals: u32,
    pub num_params: u32,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Closure {
    pub inner: Function,
    pub free: Vec<Object>,
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Type: u16 {
        const INT       = 0b00000001;
        const BOOL      = 0b00000010;
        const STRING    = 0b00000100;
        const ARRAY     = 0b00001000;
        const HASHMAP   = 0b00010000;
        const NULL      = 0b00100000;
        const FUNCTION  = 0b01000000;
        const BUILTIN   = 0b10000000;
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::INT => write!(f, "Int"),
            Self::BOOL => write!(f, "Bool"),
            Self::STRING => write!(f, "String"),
            Self::ARRAY => write!(f, "Array"),
            Self::HASHMAP => write!(f, "Hashmap"),
            Self::NULL => write!(f, "<null>"),
            Self::FUNCTION => write!(f, "Function"),
            Self::BUILTIN => write!(f, "[builtin]"),
            _ => write!(f, "todo"),
        }
    }
}
