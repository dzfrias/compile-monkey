use crate::opcode::Instructions;

#[derive(Debug)]
pub struct Frame {
    pub instrs: Instructions,
    pub ip: usize,
    pub bp: usize,
}

impl Frame {
    pub fn new(instrs: Instructions, bp: usize) -> Self {
        Self { instrs, ip: 0, bp }
    }
}
