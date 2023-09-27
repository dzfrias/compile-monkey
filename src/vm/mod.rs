pub mod error;

use crate::{
    code::{Instructions, OpCode},
    compiler::Bytecode,
    object::{Object, Type, FALSE, TRUE},
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
    last_popped: Option<Object>,
    sp: usize,
}

impl Vm {
    pub fn new(Bytecode { instrs, constants }: Bytecode) -> Self {
        Self {
            instructions: instrs,
            constants,
            stack: Vec::with_capacity(STACK_SIZE),
            sp: 0,
            last_popped: None,
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
                OpCode::Add | OpCode::Sub | OpCode::Div | OpCode::Mul => {
                    self.execute_binary_op(op)?;
                }
                OpCode::Pop => {
                    self.last_popped = self.pop();
                }
                OpCode::True => self.push(TRUE)?,
                OpCode::False => self.push(FALSE)?,
            }

            ip += 1;
        }

        Ok(())
    }

    pub fn last_popped(&self) -> Option<&Object> {
        self.last_popped.as_ref()
    }

    fn pop(&mut self) -> Option<Object> {
        self.stack.pop()
    }

    fn push(&mut self, obj: Object) -> Result<()> {
        if self.sp == STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }

        self.stack.push(obj);

        Ok(())
    }

    fn execute_binary_op(&mut self, op: OpCode) -> Result<()> {
        let right = self
            .pop()
            .expect("bytecode error: right side of add does not exist");
        let right = cast!(right, Int);
        let left = self
            .pop()
            .expect("bytecode error: left side of add does not exist");
        let left = cast!(left, Int);

        let result = match op {
            OpCode::Sub => left.checked_sub(right),
            OpCode::Add => left.checked_add(right),
            OpCode::Mul => left.checked_mul(right),
            OpCode::Div => left.checked_div(right),
            op => panic!("should not call with opcode: {op:?}"),
        };

        match result {
            Some(n) => self.push(Object::Int(n)),
            None => Err(RuntimeError::IntegerOverflow),
        }
    }

    fn read_u16(&self, start: usize) -> u16 {
        let bytes: [u8; 2] = self.instructions.as_bytes()[start..start + 2]
            .try_into()
            .expect("should be two bytes long");
        u16::from_be_bytes(bytes)
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
        ($([$input:expr, $expect:expr]),+ $(,)?) => {
            $(
                let lexer = Lexer::new($input);
                let parser = Parser::new(lexer);
                let prog = parser.parse_program().unwrap();
                let compiler = Compiler::new();
                let bytecode = compiler.compile(prog);
                let mut vm = Vm::new(bytecode);
                vm.run().expect("vm should run with no errors");
                let stack_top = vm.last_popped().unwrap();
                assert_eq!($expect, stack_top);
             )+
        };
    }

    #[test]
    fn can_execute_integer_arithmetic() {
        vm_test!(
            ["1", &Object::Int(1)],
            ["1 + 2", &Object::Int(3)],
            ["1 - 2", &Object::Int(-1)],
            ["4 / 2", &Object::Int(2)],
            ["4 * 2", &Object::Int(8)],
        );
    }

    #[test]
    fn can_eval_boolean_literals() {
        vm_test!(
            ["true", &Object::Bool(true)],
            ["false", &Object::Bool(false)],
        );
    }
}
