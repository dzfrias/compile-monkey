mod compiler;
mod frontend;
mod object;
mod opcode;
mod vm;

use anyhow::Result;
use rustyline::error::ReadlineError;

use crate::{
    compiler::{Compiler, State as CompilerState},
    frontend::{lexer::Lexer, parser::Parser},
    vm::{State as VmState, Vm},
};

fn main() -> Result<()> {
    let mut rl = rustyline::DefaultEditor::new()?;

    let mut compiler_state = CompilerState::default();
    let mut vm_state = VmState::default();

    loop {
        let readline = rl.readline(">> ");

        match readline {
            Ok(line) => {
                let lexer = Lexer::new(&line);
                let parser = Parser::new(lexer);
                let program = parser.parse_program().unwrap();
                let compiler = Compiler::new_with_state(compiler_state.clone());
                let bytecode = match compiler.compile(program) {
                    Ok(bytes) => bytes,
                    Err(err) => {
                        // Reset state
                        compiler_state = CompilerState::default();
                        vm_state = VmState::default();
                        eprintln!("{err}\n");
                        continue;
                    }
                };
                let mut vm = Vm::new_with_state(bytecode, vm_state.clone());
                if let Err(err) = vm.run() {
                    eprintln!("{err}");
                } else if let Some(top) = vm.last_popped() {
                    println!("{top}")
                }
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
