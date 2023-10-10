pub mod error;
mod frame;

use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    compiler::Bytecode,
    frontend::ast::{InfixOp, PrefixOp},
    object::{self, Closure, Function, Object, Type, FALSE, NULL, TRUE},
    opcode::OpCode,
    vm::{
        error::{Result, RuntimeError},
        frame::Frame,
    },
};

const CALLSTACK_SIZE: usize = 1024;
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
            globals: Rc::new(RefCell::new(Vec::with_capacity(GLOBALS_SIZE))),
        }
    }
}

#[derive(Debug)]
pub struct Vm {
    constants: Vec<Object>,
    state: State,
    frames: Vec<Frame>,

    stack: Vec<Object>,
    last_popped: Option<Object>,
    sp: usize,
}

impl Vm {
    pub fn new(Bytecode { instrs, constants }: Bytecode) -> Self {
        let mut frames = Vec::with_capacity(CALLSTACK_SIZE);
        let initial = Closure {
            inner: Function {
                instrs,
                num_locals: 0,
                num_params: 0,
            },
            free: vec![],
        };
        frames.push(Frame::new(initial, 0));

        Self {
            frames,
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
        while self.current_frame().ip < self.current_frame().closure.inner.instrs.as_bytes().len() {
            let ip = self.current_frame().ip;
            let op = OpCode::try_from(self.current_frame().closure.inner.instrs.as_bytes()[ip])
                .expect("bytecode error: invalid opcode");

            match op {
                OpCode::Constant => {
                    let idx = self.read_u16();
                    let constant = &self.constants[idx as usize];
                    self.push(constant.clone())?;
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
                    let pos = self.read_u16();
                    self.current_frame_mut().ip = (pos - 1) as usize;
                }
                OpCode::JumpNotTruthy => {
                    let pos = self.read_u16();
                    let cond = self
                        .pop()
                        .expect("should never compile jump with nothing on the stack");
                    if !cond.is_truthy() {
                        self.current_frame_mut().ip = (pos - 1) as usize;
                    }
                }
                OpCode::Null => self.push(NULL)?,
                OpCode::SetGlobal => {
                    let global_index = self.read_u16() as usize;
                    let obj = self
                        .pop()
                        .expect("should never set global with nothing on the stack");
                    if global_index < self.state.globals.borrow().len() {
                        self.state.globals.borrow_mut()[global_index] = obj;
                    } else {
                        self.state.globals.borrow_mut().push(obj);
                    }
                }
                OpCode::GetGlobal => {
                    let global_index = self.read_u16() as usize;
                    let global = self.state.globals.borrow_mut()[global_index].clone();
                    self.stack.push(global);
                }
                OpCode::Array => {
                    let len = self.read_u16() as usize;
                    let mut elems = vec![NULL; len];
                    for i in 1..=len {
                        elems[len - i] = self.stack.pop().unwrap();
                    }
                    self.stack.push(Object::Array(elems))
                }
                OpCode::HashMap => {
                    let mut kvs = self.read_u16() as usize;
                    // kvs contains both the amount of keys as well as the amount of values
                    let mut hashmap = HashMap::with_capacity(kvs / 2);
                    while kvs > 0 {
                        let val = self.pop().unwrap();
                        let key = self.pop().unwrap();
                        hashmap.insert(key, val);
                        kvs -= 2;
                    }
                    self.stack.push(Object::HashMap(hashmap))
                }
                OpCode::Index => {
                    let index = self.pop().unwrap();
                    let expr = self.pop().unwrap();
                    self.execute_index_expr(expr, index)?;
                }
                OpCode::Call => {
                    let argnum = self.read_u8() as usize;
                    let mut args = Vec::with_capacity(argnum);
                    for _ in 0..argnum {
                        let arg = self.pop().unwrap();
                        args.push(arg);
                    }
                    args.reverse();

                    let obj = self.pop().unwrap();

                    match obj {
                        /* Object::Function(func) |  */
                        Object::Closure(func) => {
                            let params = func.inner.num_params;
                            let locals = func.inner.num_locals;
                            self.push_frame(Frame::new(func, self.stack.len()));

                            if args.len() as u32 != params {
                                return Err(RuntimeError::WrongArgs {
                                    expected: params,
                                    got: args.len() as u32,
                                });
                            }
                            // Push args back onto the stack, as local variables
                            for arg in args {
                                self.push(arg)?;
                            }

                            for _ in 0..locals {
                                self.push(NULL)?;
                            }
                            self.sp += locals as usize + argnum;
                            // continue to not increment with new frame
                            continue;
                        }
                        Object::Builtin(builtin) => {
                            self.push(builtin(args)?)?;
                        }
                        _ => return Err(RuntimeError::UncallableType(obj.monkey_type())),
                    }
                }
                OpCode::Ret => {
                    self.pop_frame();
                    self.push(NULL)?;
                }
                OpCode::RetVal => {
                    let ret_val = self
                        .pop()
                        .expect("should have someting on the stack when returning");
                    self.pop_frame();
                    self.push(ret_val)?;
                }
                OpCode::SetLocal => {
                    let local_idx = self.read_u16();
                    // Get space reserved on the bottom of stack for locals
                    let bp = self.current_frame().bp;
                    self.stack[bp + local_idx as usize] = self.pop().unwrap();
                }
                OpCode::GetLocal => {
                    let local_idx = self.read_u16();
                    // Get space reserved on the bottom of stack for locals
                    let bp = self.current_frame().bp;
                    let obj = self.stack[bp + local_idx as usize].clone();
                    self.push(obj)?;
                }
                OpCode::GetBuiltin => {
                    let idx = self.read_u8();
                    let (_, def) = object::builtins()[idx as usize];
                    self.push(Object::Builtin(def))?;
                }
                OpCode::Closure => {
                    let idx = self.read_u16();
                    let free_len = self.read_u8() as usize;
                    let mut free = vec![NULL; free_len];
                    for i in 1..=free_len {
                        free[free_len - i] = self.pop().unwrap();
                    }
                    let constant = &self.constants[idx as usize];
                    let Object::Function(func) = constant else {
                        panic!("trying to convert non-function into a closure");
                    };
                    let closure = Closure {
                        inner: func.clone(),
                        free,
                    };
                    self.push(Object::Closure(closure))?;
                }
                OpCode::GetFree => {
                    let idx = self.read_u8();
                    let free = &self.current_frame().closure.free;
                    self.push(free[idx as usize].clone())?;
                }
                OpCode::CurrentClosure => {
                    let current = self.current_frame().closure.clone();
                    self.push(Object::Closure(current))?;
                }
            }

            self.current_frame_mut().ip += 1;
        }

        Ok(())
    }

    pub fn last_popped(&self) -> Option<&Object> {
        self.last_popped.as_ref()
    }

    fn pop(&mut self) -> Option<Object> {
        self.sp = self.sp.saturating_sub(1);
        self.stack.pop()
    }

    fn current_frame(&self) -> &Frame {
        self.frames
            .last()
            .expect("should never have an empty call stack")
    }

    fn current_frame_mut(&mut self) -> &mut Frame {
        self.frames
            .last_mut()
            .expect("should never have an empty call stack")
    }

    fn push_frame(&mut self, frame: Frame) {
        self.frames.push(frame);
    }

    fn pop_frame(&mut self) -> Frame {
        self.frames
            .pop()
            .expect("should never have an empty call stack")
    }

    fn push(&mut self, obj: Object) -> Result<()> {
        if self.sp == STACK_SIZE {
            return Err(RuntimeError::StackOverflow);
        }

        self.stack.push(obj);
        self.sp += 1;

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
            (Object::String(lhs), Object::String(rhs)) => {
                self.execute_string_infix_op(op, lhs, rhs)?
            }
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
                    lhs: Type::BOOL,
                    rhs: Type::BOOL,
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
                expr: Type::INT,
                op: opcode_to_prefix_op(op)
                    .expect("should not be called with invalid prefix opcode"),
            }),
        }
    }

    fn execute_bool_prefix_op(&mut self, op: OpCode, bool: bool) -> Result<()> {
        match op {
            OpCode::Bang => self.push(Object::Bool(!bool)),
            _ => Err(RuntimeError::InvalidType {
                expr: Type::BOOL,
                op: opcode_to_prefix_op(op)
                    .expect("should not be called with invalid prefix opcode"),
            }),
        }
    }

    fn execute_string_infix_op(&mut self, op: OpCode, lhs: String, rhs: String) -> Result<()> {
        let obj = match op {
            OpCode::Add => Object::String(lhs + &rhs),
            _ => {
                return Err(RuntimeError::InvalidTypes {
                    lhs: Type::STRING,
                    rhs: Type::STRING,
                    op: opcode_to_infix_op(op)
                        .expect("should not be called with invalid prefix opcode"),
                })
            }
        };
        self.push(obj)?;

        Ok(())
    }

    fn execute_index_expr(&mut self, expr: Object, index: Object) -> Result<()> {
        let obj = match (expr, index) {
            (Object::Array(arr), Object::Int(i)) => arr
                .get(i as usize)
                .ok_or(RuntimeError::IndexOutOfRange)?
                .clone(),
            (Object::HashMap(hashmap), obj) => hashmap.get(&obj).unwrap_or(&NULL).clone(),
            (lhs, rhs) => {
                return Err(RuntimeError::IndexNotSupported {
                    lhs: lhs.monkey_type(),
                    rhs: rhs.monkey_type(),
                })
            }
        };
        self.push(obj)?;

        Ok(())
    }

    fn read_u16(&mut self) -> u16 {
        let start = self.current_frame().ip + 1;
        let bytes: [u8; 2] = self.current_frame().closure.inner.instrs.as_bytes()[start..start + 2]
            .try_into()
            .expect("should be two bytes long");
        self.current_frame_mut().ip += 2;
        u16::from_be_bytes(bytes)
    }

    fn read_u8(&mut self) -> u8 {
        let start = self.current_frame().ip + 1;
        let bytes: [u8; 1] = self.current_frame().closure.inner.instrs.as_bytes()[start..start + 1]
            .try_into()
            .expect("should be one byte long");
        self.current_frame_mut().ip += 1;
        u8::from_be_bytes(bytes)
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
    use std::collections::HashMap;

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
                let bytecode = compiler.compile(prog).expect("should compile with no errors");
                let mut vm = Vm::new(bytecode);
                vm.run().expect("vm should run with no errors");
                let stack_top = vm.last_popped().expect("stack should have something last popped");
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

    #[test]
    fn can_eval_string_exprs() {
        vm_test!(
            ["\"hello\"", &Object::String("hello".to_owned())],
            ["\"mon\" + \"key\"", &Object::String("monkey".to_owned())],
        );
    }

    #[test]
    fn can_eval_array_exprs() {
        vm_test!(
            ["[]", &Object::Array(vec![])],
            [
                "[1, 2, 3]",
                &Object::Array(vec![Object::Int(1), Object::Int(2), Object::Int(3)])
            ],
        );
    }

    #[test]
    fn can_eval_hashmap_exprs() {
        vm_test!(
            ["{}", &Object::HashMap(HashMap::new())],
            [
                "{1: 2, 3: 4, \"hello\": 3 * 3}",
                &Object::HashMap(HashMap::from_iter([
                    (Object::Int(1), Object::Int(2)),
                    (Object::Int(3), Object::Int(4)),
                    (Object::String("hello".to_owned()), Object::Int(9))
                ]))
            ],
        );
    }

    #[test]
    fn can_eval_index_exprs() {
        vm_test!(
            ["[1, 2, 3][1]", &Object::Int(2)],
            ["{1: 2, 3: 4, \"hello\": 3 * 3}[3]", &Object::Int(4)],
        );
    }

    #[test]
    fn can_eval_call_exprs() {
        vm_test!(
            ["let func = fn() { 10 + 5 }; func()", &Object::Int(15)],
            ["let func = fn() {}; func()", &Object::Null],
            [
                "let func = fn(x, y) { let z = 1; x - y + z }; func(1, 2)",
                &Object::Int(0)
            ],
        );
    }

    #[test]
    fn can_eval_functions_with_local_bindings() {
        vm_test!(
            [
                "let one = fn() { let one = 1; one }; one()",
                &Object::Int(1)
            ],
            [
                "let one = 1; let three = fn() { return one + 2 }; three()",
                &Object::Int(3)
            ],
        );
    }

    #[test]
    fn can_eval_builtin_functions() {
        vm_test!(
            ["len([])", &Object::Int(0)],
            [
                "let x = []; push(x, 1);",
                &Object::Array(vec![Object::Int(1)])
            ],
        );
    }

    #[test]
    fn can_eval_closures() {
        vm_test!(
            ["let func = fn(a) { fn(b) { a + b } }; func(1)(2)", &Object::Int(3)],
            ["let countDown = fn(x) { if (x == 0) { return 0; } else { countDown(x - 1) } }; countDown(1)", &Object::Int(0)],
            ["let wrapper = fn() { let countDown = fn(x) { if (x == 0) { return 0; } else { countDown(x - 1) } }; countDown(1) }; wrapper()", &Object::Int(0)],
        );
    }
}
