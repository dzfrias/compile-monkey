#![allow(dead_code)]

pub mod error;

use crate::{
    code::{Instructions, OpCode},
    compiler::Bytecode,
    object::{Object, Type},
    vm::error::{Result, RuntimeError},
};

const STACK_SIZE: usize = 2048;

macro_rules! cast {
    ($obj:expr, $ty:ident) => {{
        let Object::$ty(obj) = $obj else {
            return Err(RuntimeError::ExpectedType {
                expected: Type::$ty,
                got: $obj.monkey_type(),
            });
        };
        obj
    }};
}

#[derive(Debug)]
pub struct Vm {
    instructions: Instructions,
    constants: Vec<Object>,

    stack: Vec<Object>,
    sp: usize,
}

impl Vm {
    pub fn new(Bytecode { instrs, constants }: Bytecode) -> Self {
        Self {
            instructions: instrs,
            constants,
            stack: Vec::with_capacity(STACK_SIZE),
            sp: 0,
        }
    }

    pub fn run(&mut self) -> Result<()> {
        // The VM's instruction pointer
        let mut ip = 0;
        while ip < self.instructions.as_bytes().len() {
            let op = OpCode::try_from(self.instructions.as_bytes()[ip])
                .expect("bytecode error: invalid opcode");

            match op {
                OpCode::Constant => {
                    let idx = self.read_u16(ip + 1);
                    let constant = &self.constants[idx as usize];
                    self.push(constant.clone())?;
                    ip += 2;
                }
                OpCode::Add => {
                    let right = {
                        let right = self
                            .pop()
                            .expect("bytecode error: right side of add does not exist");
                        *cast!(right, Int)
                    };
                    let left = {
                        let left = self
                            .pop()
                            .expect("bytecode error: left side of add does not exist");
                        *cast!(left, Int)
                    };

                    let sum = left + right;
                    self.push(Object::Int(sum))?;
                }
            }

            ip += 1;
        }

        Ok(())
    }

    fn pop(&mut self) -> Option<&Object> {
        self.sp -= 1;
        self.stack.get(self.sp)
    }

    fn push(&mut self, obj: Object) -> Result<()> {
        if self.sp == STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }
        // TODO: stack overflow handling
        self.stack.push(obj);
        self.sp += 1;

        Ok(())
    }

    fn read_u16(&self, start: usize) -> u16 {
        let bytes: [u8; 2] = self.instructions.as_bytes()[start..start + 2]
            .try_into()
            .expect("should be two bytes long");
        u16::from_be_bytes(bytes)
    }

    pub fn stack_top(&self) -> Option<&Object> {
        self.stack.last()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compiler::Compiler,
        frontend::{lexer::Lexer, parser::Parser},
    };

    use super::*;

    macro_rules! vm_test {
        ($([$input:expr, $expect:expr]),+) => {
            $(
                let lexer = Lexer::new($input);
                let parser = Parser::new(lexer);
                let prog = parser.parse_program().unwrap();
                let compiler = Compiler::new();
                let bytecode = compiler.compile(prog);
                let mut vm = Vm::new(bytecode);
                vm.run().expect("vm should run with no errors");
                let stack_top = vm.stack_top().unwrap();
                assert_eq!($expect, stack_top);
             )+
        };
    }

    #[test]
    fn can_execute_integer_arithmetic() {
        vm_test!(["1", &Object::Int(1)], ["1 + 2", &Object::Int(3)]);
    }
}
