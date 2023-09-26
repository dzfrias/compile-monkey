use crate::{
    code::{Instruction, Instructions, OpCode},
    frontend::ast::{Block, Expr, InfixOp, Program, Stmt},
    object::Object,
};

#[derive(Debug)]
pub struct Compiler {
    instrs: Instructions,
    constants: Vec<Object>,
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
    }

    fn compile_block(&mut self, block: &Block) {
        for stmt in &block.0 {
            self.compile_stmt(stmt);
        }
    }

    fn compile_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Expr(expr) => self.compile_expr(expr),
            stmt => todo!("compile stmt for: {stmt}"),
        }
    }

    fn compile_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Infix { left, op, right } => {
                self.compile_expr(&left);
                self.compile_expr(&right);
                match op {
                    InfixOp::Plus => self.emit(OpCode::Add, vec![]),
                    op => todo!("opcode for {op}"),
                }
            }
            Expr::IntegerLiteral(int) => {
                let obj = Object::Int(*int);
                self.constants.push(obj);
                self.emit(OpCode::Constant, vec![(self.constants.len() - 1) as u32]);
            }
            expr => todo!("compile expr for: {expr}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        code::{Instruction, OpCode},
        frontend::{lexer::Lexer, parser::Parser},
    };

    use super::*;

    macro_rules! assert_instrs {
        ($expect:expr, $got:expr) => {
            if $expect != $got {
                panic!("invalid instructions expected: {}, got: {}", $expect, $got);
            }
        };
    }

    #[test]
    fn integer_arithmetic() {
        let tests = [(
            "1 + 2",
            Bytecode {
                constants: vec![Object::Int(1), Object::Int(2)],
                instrs: Instructions::from_iter([
                    Instruction::new(OpCode::Constant, vec![0]),
                    Instruction::new(OpCode::Constant, vec![1]),
                    Instruction::new(OpCode::Add, vec![]),
                ]),
            },
        )];

        for (input, expect) in tests {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser
                .parse_program()
                .expect("input should have no parse errors");
            let compiler = Compiler::new();
            let bytecode = compiler.compile(program);
            assert_instrs!(expect.instrs, bytecode.instrs);
            assert_eq!(expect.constants, bytecode.constants);
        }
    }
}
