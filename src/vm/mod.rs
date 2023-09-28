pub mod error;

use crate::{
    code::{Instructions, OpCode},
    compiler::Bytecode,
    frontend::ast::InfixOp,
    object::{Object, Type, FALSE, TRUE},
    vm::error::{Result, RuntimeError},
};

const STACK_SIZE: usize = 2048;

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

                OpCode::Add
                | OpCode::Sub
                | OpCode::Div
                | OpCode::Mul
                | OpCode::Equal
                | OpCode::NotEqual
                | OpCode::GreaterThan => self.execute_infix_op(op)?,

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

    fn execute_infix_op(&mut self, op: OpCode) -> Result<()> {
        let right = self
            .pop()
            .expect("bytecode error: right side of add does not exist");
        let left = self
            .pop()
            .expect("bytecode error: left side of add does not exist");

        match (left, right) {
            (Object::Int(lhs), Object::Int(rhs)) => self.execute_integer_infix_op(op, lhs, rhs)?,
            (Object::Bool(lhs), Object::Bool(rhs)) => self.execute_bool_infix_op(op, lhs, rhs)?,
            (lhs, rhs) => {
                return Err(RuntimeError::InvalidTypes {
                    lhs: lhs.monkey_type(),
                    rhs: rhs.monkey_type(),
                    op: opcode_to_infix_op(op).expect("should not be called with invalid op"),
                })
            }
        }

        Ok(())
    }

    fn execute_integer_infix_op(&mut self, op: OpCode, l: i64, r: i64) -> Result<()> {
        let obj = match op {
            OpCode::Sub | OpCode::Add | OpCode::Mul | OpCode::Div => {
                let result = match op {
                    OpCode::Sub => l.checked_sub(r),
                    OpCode::Add => l.checked_add(r),
                    OpCode::Mul => l.checked_mul(r),
                    OpCode::Div => l.checked_div(r),
                    _ => unreachable!(),
                };

                match result {
                    Some(i) => Object::Int(i),
                    None => return Err(RuntimeError::IntegerOverflow),
                }
            }
            OpCode::GreaterThan => Object::Bool(l > r),
            OpCode::Equal => Object::Bool(l == r),
            OpCode::NotEqual => Object::Bool(l != r),
            op => panic!("BUG: should never have invalid integer infix operation: {op:?}"),
        };

        self.push(obj)?;

        Ok(())
    }

    fn execute_bool_infix_op(&mut self, op: OpCode, lhs: bool, rhs: bool) -> Result<()> {
        let res = match op {
            OpCode::Equal => lhs == rhs,
            OpCode::NotEqual => lhs != rhs,
            op => {
                let corresponding = opcode_to_infix_op(op)
                    .expect("BUG: should not be called with opcode that is not an infix op");
                return Err(RuntimeError::InvalidTypes {
                    lhs: Type::Bool,
                    rhs: Type::Bool,
                    op: corresponding,
                });
            }
        };

        self.push(Object::Bool(res))?;

        Ok(())
    }

    fn read_u16(&self, start: usize) -> u16 {
        let bytes: [u8; 2] = self.instructions.as_bytes()[start..start + 2]
            .try_into()
            .expect("should be two bytes long");
        u16::from_be_bytes(bytes)
    }
}

fn opcode_to_infix_op(op: OpCode) -> Option<InfixOp> {
    let corresponding = match op {
        OpCode::Add => InfixOp::Plus,
        OpCode::Sub => InfixOp::Minus,
        OpCode::Div => InfixOp::Slash,
        OpCode::Mul => InfixOp::Asterisk,
        OpCode::GreaterThan => InfixOp::Gt,
        OpCode::Equal => InfixOp::Eq,
        OpCode::NotEqual => InfixOp::NotEq,
        _ => return None,
    };
    Some(corresponding)
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
                assert_eq!($expect, stack_top, "error on input {}", $input);
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

    #[test]
    fn can_eval_boolean_infix_ops() {
        vm_test!(
            ["true == true", &Object::Bool(true)],
            ["false == true", &Object::Bool(false)],
            ["1 > 2", &Object::Bool(false)],
            ["2 < 1", &Object::Bool(false)],
            ["10 == 10", &Object::Bool(true)],
        );
    }
}
