mod code;
mod compiler;
mod env;
mod frontend;
mod object;
mod vm;

use anyhow::Result;
use rustyline::error::ReadlineError;

use crate::{
    compiler::Compiler,
    frontend::{lexer::Lexer, parser::Parser},
    vm::Vm,
};

fn main() -> Result<()> {
    let mut rl = rustyline::DefaultEditor::new()?;

    loop {
        let readline = rl.readline(">> ");

        match readline {
            Ok(line) => {
                let lexer = Lexer::new(&line);
                let parser = Parser::new(lexer);
                let program = parser.parse_program().unwrap();
                let compiler = Compiler::new();
                let bytecode = compiler.compile(program);
                let mut vm = Vm::new(bytecode);
                if let Err(runtime) = vm.run() {
                    println!("{runtime}");
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
