pub mod error;

use std::{cell::RefCell, rc::Rc};

use crate::{
    compiler::Bytecode,
    frontend::ast::{InfixOp, PrefixOp},
    object::{Object, Type, FALSE, NULL, TRUE},
    opcode::{Instructions, OpCode},
    vm::error::{Result, RuntimeError},
};

const STACK_SIZE: usize = 2048;
const GLOBALS_SIZE: usize = u16::MAX as usize;

/// Opaque type representing potential global state of the vm. The only way it can be created is
/// with State::default().
///
/// Cheap to clone.
#[derive(Debug, Clone)]
pub struct State {
    globals: Rc<RefCell<Vec<Object>>>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            globals: Rc::new(RefCell::new(vec![NULL; GLOBALS_SIZE])),
        }
    }
}

#[derive(Debug)]
pub struct Vm {
    instructions: Instructions,
    constants: Vec<Object>,
    state: State,

    stack: Vec<Object>,
    last_popped: Option<Object>,
    sp: usize,
}

impl Vm {
    pub fn new(Bytecode { instrs, constants }: Bytecode) -> Self {
        Self {
            instructions: instrs,
            constants,
            state: State::default(),
            stack: Vec::with_capacity(STACK_SIZE),
            sp: 0,
            last_popped: None,
        }
    }

    pub fn new_with_state(bytecode: Bytecode, state: State) -> Self {
        Self {
            state,
            ..Self::new(bytecode)
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

                OpCode::Minus | OpCode::Bang => self.execute_prefix_op(op)?,

                OpCode::Pop => {
                    self.last_popped = self.pop();
                }

                OpCode::True => self.push(TRUE)?,
                OpCode::False => self.push(FALSE)?,
                OpCode::Jump => {
                    let pos = self.read_u16(ip + 1);
                    ip = (pos - 1) as usize
                }
                OpCode::JumpNotTruthy => {
                    let pos = self.read_u16(ip + 1);
                    ip += 2;
                    let cond = self
                        .pop()
                        .expect("should never compile jump with nothing on the stack");
                    if !cond.is_truthy() {
                        ip = (pos - 1) as usize;
                    }
                }
                OpCode::Null => self.push(NULL)?,
                OpCode::SetGlobal => {
                    let global_index = self.read_u16(ip + 1) as usize;
                    ip += 2;
                    self.state.globals.borrow_mut()[global_index] = self
                        .pop()
                        .expect("should never set global with nothing on the stack");
                }
                OpCode::GetGlobal => {
                    let global_index = self.read_u16(ip + 1) as usize;
                    ip += 2;
                    let global = self.state.globals.borrow_mut()[global_index].clone();
                    self.stack.push(global);
                }
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

    fn execute_prefix_op(&mut self, op: OpCode) -> Result<()> {
        let expr = self
            .pop()
            .expect("bytecode error: expression side of prefix operator does not exist");

        match expr {
            Object::Int(int) => self.execute_integer_prefix_op(op, int),
            Object::Bool(bool) => self.execute_bool_prefix_op(op, bool),
            Object::Null if op == OpCode::Bang => self.push(Object::Bool(true)),

            _ => Err(RuntimeError::InvalidType {
                expr: expr.monkey_type(),
                op: opcode_to_prefix_op(op)
                    .expect("should not be called with invalid prefix opcode"),
            }),
        }
    }

    fn execute_integer_prefix_op(&mut self, op: OpCode, int: i64) -> Result<()> {
        match op {
            OpCode::Minus => self.push(Object::Int(-int)),
            _ => Err(RuntimeError::InvalidType {
                expr: Type::Int,
                op: opcode_to_prefix_op(op)
                    .expect("should not be called with invalid prefix opcode"),
            }),
        }
    }

    fn execute_bool_prefix_op(&mut self, op: OpCode, bool: bool) -> Result<()> {
        match op {
            OpCode::Bang => self.push(Object::Bool(!bool)),
            _ => Err(RuntimeError::InvalidType {
                expr: Type::Bool,
                op: opcode_to_prefix_op(op)
                    .expect("should not be called with invalid prefix opcode"),
            }),
        }
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

fn opcode_to_prefix_op(op: OpCode) -> Option<PrefixOp> {
    let corresponding = match op {
        OpCode::Minus => PrefixOp::Minus,
        OpCode::Bang => PrefixOp::Bang,
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

    #[test]
    fn can_eval_prefix_ops() {
        vm_test!(
            ["!true", &Object::Bool(false)],
            ["!false", &Object::Bool(true)],
            ["-1", &Object::Int(-1)],
            ["!(if (false) { 5 })", &Object::Bool(true)],
        );
    }

    #[test]
    fn can_eval_conditionals() {
        vm_test!(
            ["if (true) { 10 }", &Object::Int(10)],
            ["if (true) { 10 } else { 20 }", &Object::Int(10)],
            ["if (false) { 10 } else { 20 }", &Object::Int(20)],
            ["if (1 < 2) { 10 } else { 20 }", &Object::Int(10)],
            ["if (false) { 10 }", &Object::Null],
        );
    }

    #[test]
    fn can_eval_variable_bindings() {
        vm_test!(
            ["let one = 1; one", &Object::Int(1)],
            ["let one = 1; let two = 2; one + two", &Object::Int(3)],
        );
    }
}
