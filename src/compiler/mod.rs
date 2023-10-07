mod error;
mod symbol_table;

use std::{cell::RefCell, rc::Rc};

use num_enum::TryFromPrimitive;

use crate::{
    compiler::symbol_table::Scope,
    frontend::ast::{Block, Expr, InfixOp, PrefixOp, Program, Stmt},
    object::{self, Function, Object},
    opcode::{Instruction, Instructions, OpCode},
};
pub use error::{CompilerError, Result};
use symbol_table::SymbolTable;

/// Opaque type representing potential global state of the compiler. The only way it can be created
/// is with State::default().
///
/// Cheap to clone.
#[derive(Debug, Clone, Default)]
pub struct State {
    symbol_table: Rc<RefCell<SymbolTable>>,
    constants: Rc<RefCell<Vec<Object>>>,

    has_defined_builtins: bool,
}

#[derive(Debug)]
pub struct Compiler {
    state: State,

    scope_stack: Vec<CompilationScope>,
}

#[derive(Debug, PartialEq)]
pub struct Bytecode {
    pub instrs: Instructions,
    pub constants: Vec<Object>,
}

#[derive(Debug, Default)]
struct CompilationScope {
    instrs: Instructions,
    last_opcode: OpCode,
    prev_opcode: OpCode,
}

impl Compiler {
    pub fn new() -> Self {
        let mut c = Self {
            state: State::default(),
            scope_stack: vec![CompilationScope::default()],
        };
        for (i, (name, _)) in object::builtins().iter().enumerate() {
            c.state
                .symbol_table
                .borrow_mut()
                .define_builtin(name, i as u32)
        }
        c.state.has_defined_builtins = true;
        c
    }

    pub fn new_with_state(state: State) -> Self {
        let mut c = Self {
            state,
            ..Self::new()
        };
        if !c.state.has_defined_builtins {
            for (i, (name, _)) in object::builtins().iter().enumerate() {
                c.state
                    .symbol_table
                    .borrow_mut()
                    .define_builtin(name, i as u32)
            }
            c.state.has_defined_builtins = true;
        }
        c
    }

    pub fn compile(mut self, program: Program) -> Result<Bytecode> {
        self.compile_block(&(program as Block))?;
        // Roundabout way of cloning the inner value of the Rc<RefCell<_>>
        let constants = self.state.constants.borrow().iter().cloned().collect();

        Ok(Bytecode {
            instrs: self.pop_scope(),
            constants,
        })
    }

    fn enter_scope(&mut self) {
        self.scope_stack.push(CompilationScope::default());
        let old = self.state.symbol_table.replace(SymbolTable::default());
        self.state
            .symbol_table
            .replace(SymbolTable::new_enclosing(old));
    }

    fn pop_scope(&mut self) -> Instructions {
        if self.scope_stack.is_empty() {
            panic!("should not try to pop a scope that doesn't exist");
        }
        let mut old = self.state.symbol_table.replace(SymbolTable::default());
        if let Some(outer) = old.outer {
            old = *outer;
        }
        self.state.symbol_table.replace(old);
        self.scope_stack
            .pop()
            .expect("should have a compilation scope")
            .instrs
    }

    fn current_scope_mut(&mut self) -> &mut CompilationScope {
        self.scope_stack
            .last_mut()
            .expect("should have a scope on the stack")
    }

    fn current_scope(&self) -> &CompilationScope {
        self.scope_stack
            .last()
            .expect("should have a scope on the stack")
    }

    fn emit(&mut self, opcode: OpCode, operands: Vec<u32>) {
        let instr = Instruction::new(opcode, operands);
        self.current_scope_mut().instrs.add(instr);
        self.set_last_instr(opcode)
    }

    fn set_last_instr(&mut self, op: OpCode) {
        let current_scope = self.current_scope_mut();
        current_scope.prev_opcode = current_scope.last_opcode;
        current_scope.last_opcode = op;
    }

    fn change_operand(&mut self, pos: usize, operand: u32) {
        let current = self.current_scope_mut();
        let op = OpCode::try_from_primitive(current.instrs.as_bytes()[pos])
            .expect("instruction to mutate should be valid");
        let new_instr = Instruction::new(op, vec![operand]);
        current.instrs.replace_instr(pos, new_instr);
    }

    fn compile_block(&mut self, block: &Block) -> Result<()> {
        for stmt in &block.0 {
            self.compile_stmt(stmt)?;
        }

        Ok(())
    }

    fn compile_stmt(&mut self, stmt: &Stmt) -> Result<()> {
        match stmt {
            Stmt::Expr(expr) => {
                self.compile_expr(expr)?;
                self.emit(OpCode::Pop, vec![]);
            }
            Stmt::Let { ident, expr } => {
                self.compile_expr(expr)?;
                let (index, local) = {
                    let mut table = self.state.symbol_table.borrow_mut();
                    let symbol = table.define(&ident.0);
                    (symbol.index, symbol.scope == Scope::Local)
                };
                let opcode = if local {
                    OpCode::SetLocal
                } else {
                    OpCode::SetGlobal
                };
                self.emit(opcode, vec![index]);
            }
            Stmt::Return { expr } => {
                self.compile_expr(expr)?;
                self.emit(OpCode::RetVal, vec![])
            }
        }

        Ok(())
    }

    fn current_position(&self) -> usize {
        self.current_scope().instrs.as_bytes().len()
    }

    fn compile_expr(&mut self, expr: &Expr) -> Result<()> {
        match expr {
            Expr::Infix { left, op, right } => {
                if *op == InfixOp::Lt {
                    self.compile_expr(&right)?;
                    self.compile_expr(&left)?;
                } else {
                    self.compile_expr(&left)?;
                    self.compile_expr(&right)?;
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
                    op => panic!("opcode for {op}"),
                };
                self.emit(opcode, vec![]);
            }
            Expr::Prefix { op, expr } => {
                self.compile_expr(expr)?;
                let opcode = match op {
                    PrefixOp::Bang => OpCode::Bang,
                    PrefixOp::Minus => OpCode::Minus,
                    PrefixOp::Plus => return Ok(()),
                };
                self.emit(opcode, vec![]);
            }
            Expr::StringLiteral(literal) => {
                let obj = Object::String(literal.clone());
                self.state.constants.borrow_mut().push(obj);
                let len = self.state.constants.borrow().len();
                self.emit(OpCode::Constant, vec![(len - 1) as u32]);
            }
            Expr::IntegerLiteral(int) => {
                let obj = Object::Int(*int);
                self.state.constants.borrow_mut().push(obj);
                let len = self.state.constants.borrow().len();
                self.emit(OpCode::Constant, vec![(len - 1) as u32]);
            }
            Expr::BooleanLiteral(bool) => {
                let opcode = match bool {
                    true => OpCode::True,
                    false => OpCode::False,
                };
                self.emit(opcode, vec![]);
            }
            Expr::ArrayLiteral(arr) => {
                for elem in arr {
                    self.compile_expr(elem)?;
                }
                self.emit(OpCode::Array, vec![arr.len() as u32]);
            }
            Expr::HashLiteral(key_vals) => {
                for (key, val) in key_vals {
                    self.compile_expr(key)?;
                    self.compile_expr(val)?;
                }
                let total_len = key_vals.len() * 2;
                self.emit(OpCode::HashMap, vec![total_len as u32]);
            }
            Expr::If {
                condition,
                consequence,
                alternative,
            } => {
                self.compile_expr(condition)?;
                let jump_pos = self.current_position();
                self.emit(OpCode::JumpNotTruthy, vec![9999]);
                self.compile_block(consequence)?;
                {
                    let current = self.current_scope_mut();
                    if current.last_opcode == OpCode::Pop {
                        current.instrs.pop();
                        current.last_opcode = current.prev_opcode;
                    }
                }

                // Position of the consequence jump instruction
                let cons_jump_pos = self.current_position();
                self.emit(OpCode::Jump, vec![9999]);
                // Change operand of the conditional jump instruction to after the
                // consequence
                self.change_operand(jump_pos, self.current_position() as u32);
                if let Some(alt) = alternative {
                    self.compile_block(alt)?;
                } else {
                    self.emit(OpCode::Null, vec![]);
                }
                {
                    let current = self.current_scope_mut();
                    if current.last_opcode == OpCode::Pop {
                        current.instrs.pop();
                        current.last_opcode = current.prev_opcode;
                    }
                }
                // Change the operand of the consequence operand to the current position
                // (after alt)
                self.change_operand(cons_jump_pos, self.current_position() as u32);
            }
            Expr::Identifier(ident) => {
                let (index, scope) = {
                    let table = &self.state.symbol_table.borrow();
                    let symbol = table.resolve(&ident.0);

                    match symbol {
                        Some(sym) => (sym.index, sym.scope),
                        None => {
                            return Err(CompilerError::UnboundVariable {
                                name: ident.0.clone(),
                            })
                        }
                    }
                };
                let opcode = match scope {
                    Scope::Local => OpCode::GetLocal,
                    Scope::Global => OpCode::GetGlobal,
                    Scope::Builtin => OpCode::GetBuiltin,
                };
                self.emit(opcode, vec![index])
            }
            Expr::Index { expr, index } => {
                self.compile_expr(expr)?;
                self.compile_expr(index)?;
                self.emit(OpCode::Index, vec![]);
            }
            Expr::Function { params, body } => {
                // Special case: no body
                if body.0.is_empty() {
                    let function = Object::Function(Function {
                        instrs: Instructions::from_iter([Instruction::new(OpCode::Ret, vec![])]),
                        num_locals: 0,
                        num_params: params.len() as u32,
                    });
                    self.state.constants.borrow_mut().push(function);
                    let len = self.state.constants.borrow().len() - 1;
                    self.emit(OpCode::Constant, vec![len as u32]);
                    return Ok(());
                }

                self.enter_scope();

                for param in params {
                    self.state.symbol_table.borrow_mut().define(&param.0);
                }
                self.compile_block(body)?;
                // If it ends with an Pop, replace it with RetVal, because of implicit returns
                if self.current_scope().last_opcode == OpCode::Pop {
                    self.current_scope_mut().instrs.pop();
                    self.emit(OpCode::RetVal, vec![]);
                    self.current_scope_mut().last_opcode = OpCode::RetVal;
                }

                let num_locals = self.state.symbol_table.borrow().locals();
                let body = self.pop_scope();
                let function = Object::Function(Function {
                    instrs: body,
                    num_locals,
                    num_params: params.len() as u32,
                });
                self.state.constants.borrow_mut().push(function);
                let len = self.state.constants.borrow().len() - 1;
                self.emit(OpCode::Constant, vec![len as u32])
            }
            Expr::Call { func, args } => {
                self.compile_expr(&func)?;
                for arg in args {
                    self.compile_expr(arg)?;
                }
                self.emit(OpCode::Call, vec![args.len() as u32]);
            }
        }

        Ok(())
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
        ($expect:expr, $got:expr, $input:expr) => {
            if $expect != $got {
                panic!(
                    "invalid instructions expected: {}, got: {}, with input: {}",
                    $expect, $got, $input
                );
            }
        };
    }

    macro_rules! make_instrs {
        ($(($opcode:ident$(, [$($operand:expr),*])?)),* $(,)?) => {
            Instructions::from_iter([
                $(
                    Instruction::new(OpCode::$opcode, vec![$($($operand,)*)?]),
                 )*
            ])
        };
    }

    macro_rules! compiler_tests {
        ($([$input:expr, { constants: $consts:expr, instrs: [$($instrs:tt)*] }]),+ $(,)?) => {
            $(
                let lexer = Lexer::new($input);
                let parser = Parser::new(lexer);
                let program = parser
                    .parse_program()
                    .expect("input should have no parse errors");
                let compiler = Compiler::new();
                let bytecode = compiler.compile(program).expect("should compile with no errors");
                let expect = Bytecode {
                    constants: $consts.into(),
                    instrs: make_instrs!($($instrs)*),
                };
                assert_instrs!(expect.instrs, bytecode.instrs, $input);
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

    #[test]
    fn bindings() {
        compiler_tests!(
            [
                "let one = 1; let two = 2;",
                {
                    constants: [Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (SetGlobal, [0]),
                        (Constant, [1]),
                        (SetGlobal, [1]),
                    ]
                }
            ],
            [
                "let one = 1; one",
                {
                    constants: [Object::Int(1)],
                    instrs: [
                        (Constant, [0]),
                        (SetGlobal, [0]),
                        (GetGlobal, [0]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn string_exprs() {
        compiler_tests!(
            [
                "\"message\"",
                {
                    constants: [Object::String("message".to_owned())],
                    instrs: [
                        (Constant, [0]),
                        (Pop),
                    ]
                }
            ],
            [
                "\"mon\" + \"key\"",
                {
                    constants: [Object::String("mon".to_owned()), Object::String("key".to_owned())],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Add),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn array_literals() {
        compiler_tests!(
            [
                "[]",
                {
                    constants: [],
                    instrs: [
                        (Array, [0]),
                        (Pop),
                    ]
                }
            ],
            [
                "[1, 2, 3]",
                {
                    constants: [Object::Int(1), Object::Int(2), Object::Int(3)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Constant, [2]),
                        (Array, [3]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn hashmap_literals() {
        compiler_tests!(
            [
                "{}",
                {
                    constants: [],
                    instrs: [
                        (HashMap, [0]),
                        (Pop),
                    ]
                }
            ],
            [
                "{1: 2, 3: 4, 5: 6 + 7}",
                {
                    constants: [Object::Int(1), Object::Int(2), Object::Int(3), Object::Int(4), Object::Int(5), Object::Int(6), Object::Int(7)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Constant, [2]),
                        (Constant, [3]),
                        (Constant, [4]),
                        (Constant, [5]),
                        (Constant, [6]),
                        (Add),
                        (HashMap, [6]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn index_exprs() {
        compiler_tests!(
            [
                "[1, 2, 3][1 + 1]",
                {
                    constants: [Object::Int(1), Object::Int(2), Object::Int(3), Object::Int(1), Object::Int(1)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (Constant, [2]),
                        (Array, [3]),
                        (Constant, [3]),
                        (Constant, [4]),
                        (Add),
                        (Index),
                        (Pop),
                    ]
                }
            ],
            [
                "{1: 2}[2 - 1]",
                {
                    constants: [Object::Int(1), Object::Int(2), Object::Int(2), Object::Int(1)],
                    instrs: [
                        (Constant, [0]),
                        (Constant, [1]),
                        (HashMap, [2]),
                        (Constant, [2]),
                        (Constant, [3]),
                        (Sub),
                        (Index),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn function_literals() {
        compiler_tests!(
            [
                "fn() { return 5 + 10; }",
                {
                    constants: [Object::Int(5), Object::Int(10), Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Constant, [0]),
                                (Constant, [1]),
                                (Add),
                                (RetVal),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [2]),
                        (Pop),
                    ]
                }
            ],
            [
                "fn() { 1; 2 }",
                {
                    constants: [Object::Int(1), Object::Int(2), Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Constant, [0]),
                                (Pop),
                                (Constant, [1]),
                                (RetVal),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [2]),
                        (Pop),
                    ]
                }
            ],
            [
                "fn() {}",
                {
                    constants: [Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Ret),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [0]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn function_calls() {
        compiler_tests!(
            [
                "fn() {}()",
                {
                    constants: [Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Ret),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [0]),
                        (Call, [0]),
                        (Pop),
                    ]
                }
            ],
            [
                "let x = fn() {};
                x();",
                {
                    constants: [Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Ret),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [0]),
                        (SetGlobal, [0]),
                        (GetGlobal, [0]),
                        (Call, [0]),
                        (Pop),
                    ]
                }
            ],
            [
                "let x = fn(x, y) { x + y };
                x(1, 2);",
                {
                    constants: [Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (GetLocal, [0]),
                                (GetLocal, [1]),
                                (Add),
                                (RetVal),
                            )
                        },
                        num_locals: 2,
                        num_params: 2,
                    }), Object::Int(1), Object::Int(2)],
                    instrs: [
                        (Constant, [0]),
                        (SetGlobal, [0]),
                        (GetGlobal, [0]),
                        (Constant, [1]),
                        (Constant, [2]),
                        (Call, [2]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn local_variables() {
        compiler_tests!(
            [
                "let x = 1; fn() { x }",
                {
                    constants: [Object::Int(1), Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (GetGlobal, [0]),
                                (RetVal),
                            )
                        },
                        num_locals: 0,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [0]),
                        (SetGlobal, [0]),
                        (Constant, [1]),
                        (Pop),
                    ]
                }
            ],
            [
                "fn() { let num = 55; num }",
                {
                    constants: [Object::Int(55), Object::Function(Function {
                        instrs: {
                            make_instrs!(
                                (Constant, [0]),
                                (SetLocal, [0]),
                                (GetLocal, [0]),
                                (RetVal),
                            )
                         },
                        num_locals: 1,
                        num_params: 0,
                    })],
                    instrs: [
                        (Constant, [1]),
                        (Pop),
                    ]
                }
            ],
        );
    }

    #[test]
    fn builtin_functions() {
        compiler_tests!(
            [
                "len([]);
                push([], 1);",
                {
                    constants: [Object::Int(1)],
                    instrs: [
                        (GetBuiltin, [0]),
                        (Array, [0]),
                        (Call, [1]),
                        (Pop),
                        (GetBuiltin, [4]),
                        (Array, [0]),
                        (Constant, [0]),
                        (Call, [2]),
                        (Pop),
                    ]
                }
            ],
        );
    }
}
