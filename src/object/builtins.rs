#![allow(unused_imports)]

use crate::{
    object::{Object, Type, NULL},
    vm::error::{Result, RuntimeError},
};

pub type Builtin = fn(Vec<Object>) -> Result<Object>;

pub fn get_builtin(name: &str) -> Option<Builtin> {
    match name {
        "len" => Some(monkey_len),
        "first" => Some(monkey_first),
        "last" => Some(monkey_last),
        "rest" => Some(monkey_rest),
        "push" => Some(monkey_push),
        "puts" => Some(monkey_puts),
        _ => None,
    }
}

pub fn builtins() -> &'static [(&'static str, Builtin)] {
    &[
        ("len", monkey_len),
        ("first", monkey_first),
        ("last", monkey_last),
        ("rest", monkey_rest),
        ("push", monkey_push),
        ("puts", monkey_puts),
    ]
}

macro_rules! validate_args_len {
    ($args:expr, $expected:expr) => {
        if $args.len() != $expected {
            return Err(RuntimeError::WrongArgs {
                expected: $expected,
                got: $args.len() as u32,
            });
        }
    };
}

fn monkey_len(args: Vec<Object>) -> Result<Object> {
    validate_args_len!(args, 1);
    match &args[0] {
        Object::String(s) => Ok(Object::Int(s.len() as i64)),
        Object::Array(arr) => Ok(Object::Int(arr.len() as i64)),
        _ => Err(RuntimeError::WrongArgType {
            got: args[0].monkey_type(),
            want: Type::ARRAY | Type::STRING,
        }),
    }
}

fn monkey_first(args: Vec<Object>) -> Result<Object> {
    validate_args_len!(args, 1);
    match &args[0] {
        Object::Array(arr) => Ok(arr.first().unwrap_or(&NULL).clone()),
        Object::String(s) => match s.chars().next() {
            Some(ch) => Ok(Object::String(ch.to_string())),
            None => Ok(Object::Null),
        },
        _ => Err(RuntimeError::WrongArgType {
            got: args[0].monkey_type(),
            want: Type::ARRAY | Type::STRING,
        }),
    }
}

fn monkey_last(args: Vec<Object>) -> Result<Object> {
    validate_args_len!(args, 1);
    match &args[0] {
        Object::Array(arr) => Ok(arr.last().unwrap_or(&NULL).clone()),
        Object::String(s) => match s.chars().last() {
            Some(ch) => Ok(Object::String(ch.to_string())),
            None => Ok(Object::Null),
        },
        _ => Err(RuntimeError::WrongArgType {
            got: args[0].monkey_type(),
            want: Type::ARRAY | Type::STRING,
        }),
    }
}

fn monkey_rest(args: Vec<Object>) -> Result<Object> {
    validate_args_len!(args, 1);
    match &args[0] {
        Object::Array(arr) => Ok(Object::Array(arr[1..].to_vec())),
        Object::String(s) => Ok(Object::String(s[1..].to_owned())),
        _ => Err(RuntimeError::WrongArgType {
            got: args[0].monkey_type(),
            want: Type::ARRAY | Type::STRING,
        }),
    }
}

fn monkey_push(args: Vec<Object>) -> Result<Object> {
    validate_args_len!(args, 2);
    match &args[0] {
        Object::Array(arr) => {
            let mut new = arr.clone();
            new.push(args[1].clone());
            Ok(Object::Array(new))
        }
        _ => Err(RuntimeError::WrongArgType {
            got: args[0].monkey_type(),
            want: Type::ARRAY,
        }),
    }
}

fn monkey_puts(args: Vec<Object>) -> Result<Object> {
    for arg in args {
        println!("{arg}");
    }
    Ok(NULL)
}
