#![allow(dead_code)]

mod env;

use crate::frontend::ast::*;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    rc::Rc,
};

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
    Function {
        params: Vec<Identifier>,
        body: Block,
        env: Rc<RefCell<Env>>,
    },
    Builtin,
}

impl Object {
    pub fn monkey_type(&self) -> Type {
        match self {
            Self::Int(_) => Type::Int,
            Self::Bool(_) => Type::Bool,
            Self::String(_) => Type::String,
            Self::Array(_) => Type::Array,
            Self::HashMap(_) => Type::HashMap,
            Self::Null => Type::Null,
            Self::Function { .. } => Type::Function,
            Self::Builtin { .. } => Type::Builtin,
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
            Self::Function { params, body, .. } => {
                let joined = params
                    .iter()
                    .map(|ident| ident.to_string() + ", ")
                    .collect::<String>();
                write!(
                    f,
                    "fn({}) {{\n {body} \n}}",
                    joined
                        .strip_suffix(", ")
                        .expect("Should always have a trailing ', '")
                )
            }
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

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum Type {
    Int,
    Bool,
    String,
    Array,
    HashMap,
    Null,
    Function,
    Builtin,
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Bool => write!(f, "Bool"),
            Self::String => write!(f, "String"),
            Self::Array => write!(f, "Array"),
            Self::HashMap => write!(f, "Hashmap"),
            Self::Null => write!(f, "<null>"),
            Self::Function => write!(f, "Function"),
            Self::Builtin => write!(f, "[builtin]"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSignature(pub HashSet<Type>);

impl fmt::Display for TypeSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let joined = self
            .0
            .iter()
            .map(|elem| elem.to_string() + " | ")
            .collect::<String>();
        write!(
            f,
            "{}",
            joined
                .strip_suffix(" | ")
                .expect("Should always have trailing ' | '")
        )
    }
}
