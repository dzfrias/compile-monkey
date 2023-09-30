use num_enum::TryFromPrimitive;

use crate::{
    frontend::ast::{Block, Expr, InfixOp, PrefixOp, Program, Stmt},
    object::Object,
    opcode::{Instruction, Instructions, OpCode},
};

#[derive(Debug)]
pub struct Compiler {
    instrs: Instructions,
    constants: Vec<Object>,

    last_opcode: OpCode,
    prev_opcode: OpCode,
}

#[derive(Debug, PartialEq)]
pub struct Bytecode {
    pub instrs: Instructions,
    pub constants: Vec<Object>,
}

impl Compiler {
    pub fn new() -> Self {
        Self {
            instrs: Instructions::default(),
            constants: vec![],

            last_opcode: OpCode::Add,
            prev_opcode: OpCode::Add,
        }
    }

    pub fn compile(mut self, program: Program) -> Bytecode {
        self.compile_block(&(program as Block));
        Bytecode {
            instrs: self.instrs,
            constants: self.constants,
        }
    }

    fn emit(&mut self, opcode: OpCode, operands: Vec<u32>) {
        let instr = Instruction::new(opcode, operands);
        self.instrs.add(instr);
        self.set_last_instr(opcode)
    }

    fn set_last_instr(&mut self, op: OpCode) {
        self.prev_opcode = self.last_opcode;
        self.last_opcode = op;
    }

    fn change_operand(&mut self, pos: usize, operand: u32) {
        let op = OpCode::try_from_primitive(self.instrs.as_bytes()[pos])
            .expect("instruction to mutate should be valid");
        let new_instr = Instruction::new(op, vec![operand]);
        self.instrs.replace_instr(pos, new_instr);
    }

    fn compile_block(&mut self, block: &Block) {
        for stmt in &block.0 {
            self.compile_stmt(stmt);
        }
    }

    fn compile_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(expr) => {
                self.compile_expr(expr);
                self.emit(OpCode::Pop, vec![]);
            }
            stmt => todo!("compile stmt for: {stmt}"),
        }
    }

    fn current_position(&self) -> usize {
        self.instrs.as_bytes().len()
    }

    fn compile_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Infix { left, op, right } => {
                if *op == InfixOp::Lt {
                    self.compile_expr(&right);
                    self.compile_expr(&left);
                } else {
                    self.compile_expr(&left);
                    self.compile_expr(&right);
                }
                let opcode = match op {
                    InfixOp::Plus => OpCode::Add,
                    InfixOp::Minus => OpCode::Sub,
                    InfixOp::Slash => OpCode::Div,
                    InfixOp::Asterisk => OpCode::Mul,
                    InfixOp::Gt => OpCode::GreaterThan,
                    InfixOp::Eq => OpCode::Equal,
                    InfixOp::NotEq => OpCode::NotEqual,
                    InfixOp::Lt => OpCode::GreaterThan,
                    op => todo!("opcode for {op}"),
                };
                self.emit(opcode, vec![]);
            }
            Expr::Prefix { op, expr } => {
                self.compile_expr(expr);
                let opcode = match op {
                    PrefixOp::Bang => OpCode::Bang,
                    PrefixOp::Minus => OpCode::Minus,
                    PrefixOp::Plus => return,
                };
                self.emit(opcode, vec![]);
            }
            Expr::IntegerLiteral(int) => {
                let obj = Object::Int(*int);
                self.constants.push(obj);
                self.emit(OpCode::Constant, vec![(self.constants.len() - 1) as u32]);
            }
            Expr::BooleanLiteral(bool) => {
                let opcode = match bool {
                    true => OpCode::True,
                    false => OpCode::False,
                };
                self.emit(opcode, vec![]);
            }
            Expr::If {
                condition,
                consequence,
                alternative,
            } => {
                self.compile_expr(condition);
                let jump_pos = self.current_position();
                self.emit(OpCode::JumpNotTruthy, vec![9999]);
                self.compile_block(consequence);
                if self.last_opcode == OpCode::Pop {
                    self.instrs.pop();
                    self.last_opcode = self.prev_opcode;
                }

                // Position of the consequence jump instruction
                let cons_jump_pos = self.current_position();
                self.emit(OpCode::Jump, vec![9999]);
                // Change operand of the conditional jump instruction to after the
                // consequence
                self.change_operand(jump_pos, self.current_position() as u32);
                if let Some(alt) = alternative {
                    self.compile_block(alt);
                } else {
                    self.emit(OpCode::Null, vec![]);
                }
                if self.last_opcode == OpCode::Pop {
                    self.instrs.pop();
                    self.last_opcode = self.prev_opcode;
                }
                // Change the operand of the consequence operand to the current position
                // (after alt)
                self.change_operand(cons_jump_pos, self.current_position() as u32);
            }
            expr => todo!("compile expr for: {expr}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        frontend::{lexer::Lexer, parser::Parser},
        opcode::{Instruction, OpCode},
    };

    use super::*;

    macro_rules! assert_instrs {
        ($expect:expr, $got:expr) => {
            if $expect != $got {
                panic!("invalid instructions expected: {}, got: {}", $expect, $got);
            }
        };
    }

    macro_rules! compiler_tests {
        ($([$input:expr, { constants: $consts:expr, instrs: [$(($opcode:ident$(, [$($operand:expr),*])?)),* $(,)?] }]),+ $(,)?) => {
            $(
                let lexer = Lexer::new($input);
                let parser = Parser::new(lexer);
                let program = parser
                    .parse_program()
                    .expect("input should have no parse errors");
                let compiler = Compiler::new();
                let bytecode = compiler.compile(program);
                let expect = Bytecode {
                    constants: $consts.into(),
                    instrs: Instructions::from_iter([
                        $(
                            Instruction::new(OpCode::$opcode, vec![$($($operand,)*)?]),
                         )*
                    ]),
                };
                assert_instrs!(expect.instrs, bytecode.instrs);
                assert_eq!(expect.constants, bytecode.constants, "invalid constant pool for input {}", $input);
             )+
        };
    }

    #[test]
    fn integer_arithmetic() {
        compiler_tests!(
            [
                "1 + 2",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Add),
                        (Pop),
                    ]
                }
            ],
            [
                "1 - 2",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Sub),
                        (Pop),
                    ]
                }
            ],
            [
                "1 / 2",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Div),
                        (Pop),
                    ]
                }
            ],
            [
                "1 * 2",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Mul),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn boolean_literals() {
        compiler_tests!(
            [
                "true",
                {
                    constants: [],
                    instrs: [
                        (True),
                        (Pop),
                    ]
                }
            ],
            [
                "false",
                {
                    constants: [],
                    instrs: [
                        (False),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn boolean_infix_exprs() {
        compiler_tests!(
            [
                "1 > 2",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (GreaterThan),
                        (Pop),
                    ]
                }
            ],
            [
                "1 < 2",
                {
                    constants: [Object::Int(2), Object::Int(1)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (GreaterThan),
                        (Pop),
                    ]
                }
            ],
            [
                "true == false",
                {
                    constants: [],
                    instrs: [
                        (True),
                        (False),
                        (Equal),
                        (Pop),
                    ]
                }
            ],
            [
                "true != false",
                {
                    constants: [],
                    instrs: [
                        (True),
                        (False),
                        (NotEqual),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn prefix_exprs() {
        compiler_tests!(
            [
                "-1",
                {
                    constants: [Object::Int(1)],
                    instrs: [
                        (Constant, [0]),
                        (Minus),
                        (Pop),
                    ]
                }
            ],
            [
                "!true",
                {
                    constants: [],
                    instrs: [
                        (True),
                        (Bang),
                        (Pop),
                    ]
                }
            ]
        );
    }

    #[test]
    fn conditionals() {
        compiler_tests!(
            [
                "if (true) { 10 }; 3333;",
                {
                    constants: [Object::Int(10), Object::Int(3333)],
                    instrs: [
                        (True),
                        (JumpNotTruthy, [10]),
                        (Constant, [0]), // 0010
                        (Jump, [11]),
                        (Null),
                        (Pop), // 0011

                        (Constant, [1]),
                        (Pop),
                    ]
                }
            ],
            [
                "if (true) { 10 } else { 20 }; 3333;",
                {
                    constants: [Object::Int(10), Object::Int(20), Object::Int(3333)],
                    instrs: [
                        (True),
                        (JumpNotTruthy, [10]),
                        (Constant, [0]),
                        (Jump, [13]),
                        (Constant, [1]), // 0010
                        (Pop), // 0013

                        (Constant, [2]),
                        (Pop),
                    ]
                }
            ],
        );
    }
}
