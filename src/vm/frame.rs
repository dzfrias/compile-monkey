use crate::object::Closure;

#[derive(Debug)]
pub struct Frame {
    pub closure: Closure,
    pub ip: usize,
    pub bp: usize,
}

impl Frame {
    pub fn new(instrs: Closure, bp: usize) -> Self {
        Self {
            closure: instrs,
            ip: 0,
            bp,
        }
    }
}
