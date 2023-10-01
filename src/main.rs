mod compiler;
mod frontend;
mod object;
mod opcode;
mod vm;

use anyhow::Result;
use rustyline::error::ReadlineError;

use crate::{
    compiler::{Compiler, SymbolTable},
    frontend::{lexer::Lexer, parser::Parser},
    vm::Vm,
};

fn main() -> Result<()> {
    let mut rl = rustyline::DefaultEditor::new()?;

    let mut symbol_table = SymbolTable::new();
    let mut constants = vec![];
    // TODO: no longer initialize memory like this. Should panic on invalid access
    let mut globals = vec![object::NULL; u16::MAX as usize];

    loop {
        let readline = rl.readline(">> ");

        match readline {
            Ok(line) => {
                let lexer = Lexer::new(&line);
                let parser = Parser::new(lexer);
                let program = parser.parse_program().unwrap();
                let compiler = Compiler::new_with_state(symbol_table.clone(), constants.clone());
                let (bytecode, sym_tbl) = compiler.compile(program);
                // TODO: Wrap this in a compiler::State type that uses Rc<RefCell<_>> for this
                // global mutable data. The cloning here is potentially expensive. Also, messing
                // with the return value of compiler.compile() is not great.
                symbol_table = sym_tbl;
                constants = bytecode.constants.clone();
                let mut vm = Vm::new(bytecode);
                // TODO: same as above
                vm.globals = globals.clone();
                if let Err(err) = vm.run() {
                    eprintln!("{err}");
                } else if let Some(top) = vm.last_popped() {
                    println!("{top}")
                }
                globals = vm.globals;
                println!()
            }
            Err(ReadlineError::Eof) => break,
            Err(ReadlineError::Interrupted) => break,
            Err(err) => {
                anyhow::bail!("error reading input: {err}");
            }
        }
    }

    Ok(())
}
