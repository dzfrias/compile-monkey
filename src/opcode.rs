#![allow(non_upper_case_globals)]

use std::fmt;

use num_enum::TryFromPrimitive;

#[derive(Clone, PartialEq)]
pub struct Instruction(Vec<u8>);

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Instructions(Vec<u8>);

impl Instruction {
    pub fn new(opcode: OpCode, operands: Vec<u32>) -> Self {
        let def = opcode.definition();

        let instr_len: usize = 1 + def
            .op_widths
            .iter()
            .map(|width| *width as usize)
            .sum::<usize>();
        let mut instr = vec![0; instr_len.into()];
        instr[0] = opcode as u8;

        let mut offset = 1;
        for (op, width) in operands.iter().zip(def.op_widths) {
            match width {
                OpWidth::HalfWord => {
                    let bytes = u16::try_from(*op)
                        .expect("operand should be two bytes wide")
                        .to_be_bytes();
                    instr[offset..offset + 2].copy_from_slice(&bytes);
                }
                OpWidth::Byte => {
                    let byte = u8::try_from(*op)
                        .expect("operand should be one byte wide")
                        .to_be_bytes();
                    instr[offset] = byte[0];
                }
            }
            offset += *width as usize
        }

        Self(instr)
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl Instructions {
    pub fn add(&mut self, instr: Instruction) {
        self.0.extend_from_slice(instr.as_bytes());
    }

    pub fn pop(&mut self) -> Option<u8> {
        self.0.pop()
    }

    pub fn replace_instr(&mut self, pos: usize, new: Instruction) {
        self.replace_bytes(pos, new.as_bytes());
    }

    pub fn replace_bytes(&mut self, pos: usize, bytes: &[u8]) {
        self.0[pos..pos + bytes.len()].copy_from_slice(&bytes);
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl fmt::Display for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let bytes = self.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            let op = OpCode::try_from(bytes[i]).expect("bytes should be valid");
            let mut operands = vec![];
            let def = op.definition();
            let mut offset = 0;
            for width in def.op_widths {
                let i = i + offset + 1;
                let width_num = *width as usize;
                let bytes = &bytes[i..i + width_num];
                let mut u32_bytes = [0; 4];
                u32_bytes[4 - width_num..].copy_from_slice(bytes);
                let op = u32::from_be_bytes(u32_bytes);
                operands.push(op);
                offset += width_num;
            }
            write!(f, "{i:0>4} {}", def.name)?;
            for op in operands {
                write!(f, " {op}")?;
            }
            writeln!(f)?;
            i += 1 + offset
        }

        Ok(())
    }
}

impl FromIterator<Instruction> for Instructions {
    fn from_iter<T: IntoIterator<Item = Instruction>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut bytes = Vec::with_capacity(iter.size_hint().0);
        for instr in iter {
            bytes.extend_from_slice(instr.as_bytes());
        }
        Self(bytes)
    }
}

/// An opcode in the monkey VM.
#[derive(Debug, TryFromPrimitive, Clone, Copy, PartialEq, Default)]
#[repr(u8)]
pub enum OpCode {
    /// Pull an object from the constant pool [u16]
    Constant,
    /// Add the top two objects on the stack
    Add,
    /// Subtract the top two objects on the stack
    Sub,
    /// Add the top two objects on the stack
    Div,
    /// Subtract the top two objects on the stack
    Mul,
    /// Pop the top of the stack
    Pop,
    /// Push the boolean `True` on the stack
    True,
    /// Push the boolean `False` on the stack
    False,
    /// Check if the top two objects on the stack are equal
    Equal,
    /// Check if the top two objects on the stack are not equal
    NotEqual,
    /// Check if the second to top object on the stack is greater than the top object on the stack.
    GreaterThan,
    /// - prefix operator
    Minus,
    /// Not prefix operator
    Bang,
    /// Jump to instruction [u16]
    Jump,
    /// Jump to instruction if the object on the stack is not truthy [u16]
    JumpNotTruthy,
    /// Push the null object onto the stack.
    #[default]
    Null,
    /// Set a global variable to the top of the stack [u16]
    SetGlobal,
    /// Get a global variable with the corresponding id [u16]
    GetGlobal,
    /// Initialize a new array with N elements [N: u16]
    Array,
    /// Initialize a new hashmap with N / 2 key-value pairs [N: u16]
    HashMap,
    /// Index the second object on the stack with the first object on the stack
    Index,
    /// Call the function on the stack [u8]
    Call,
    /// Return the value on the stack.
    RetVal,
    /// Return from the current function.
    Ret,
    /// Set a local variable to the top of the stack [u16]
    SetLocal,
    /// Get a local variable corresponding to the passed-in id [u16]
    GetLocal,
    /// Push a builtin onto the stack [u8]
    GetBuiltin,
    /// Create a closure [u16, u8]
    Closure,
    /// Get a free variable [u8]
    GetFree,
    /// Push the currently executing closure onto the stack
    CurrentClosure,
}

#[derive(Debug, Clone)]
pub struct Definition {
    pub name: &'static str,
    pub op_widths: &'static [OpWidth],
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum OpWidth {
    Byte = 1,
    HalfWord = 2,
}

impl OpCode {
    pub fn definition(&self) -> Definition {
        macro_rules! build_defs {
            ($op:expr, $($name:ident: [$($width:expr),*]),+ $(,)?) => {
                match $op {
                    $(
                        Self::$name => Definition {
                            name: stringify!($name),
                            op_widths: &[$($width),*],
                        },
                    )+
                }
            };
        }

        build_defs!(self,
            Constant: [OpWidth::HalfWord],
            Pop: [],
            Add: [],
            Sub: [],
            Div: [],
            Mul: [],
            True: [],
            False: [],
            Equal: [],
            NotEqual: [],
            GreaterThan: [],
            Minus: [],
            Bang: [],
            Jump: [OpWidth::HalfWord],
            JumpNotTruthy: [OpWidth::HalfWord],
            Null: [],
            SetGlobal: [OpWidth::HalfWord],
            GetGlobal: [OpWidth::HalfWord],
            Array: [OpWidth::HalfWord],
            HashMap: [OpWidth::HalfWord],
            Index: [],
            Call: [OpWidth::Byte],
            Ret: [],
            RetVal: [],
            SetLocal: [OpWidth::HalfWord],
            GetLocal: [OpWidth::HalfWord],
            GetBuiltin: [OpWidth::Byte],
            Closure: [OpWidth::HalfWord, OpWidth::Byte],
            GetFree: [OpWidth::Byte],
            CurrentClosure: [],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn can_make_instruction_big_endian() {
        let tests = [(
            OpCode::Constant,
            &[65534],
            &[OpCode::Constant as u8, 255, 254],
        )];
        for (op, operands, expected) in tests {
            let instr = Instruction::new(op, operands.to_vec());
            for (expect, got) in expected.iter().zip(&instr.0) {
                assert_eq!(expect, got)
            }
        }
    }

    #[test]
    fn instrs_to_string() {
        let instrs = Instructions::from_iter([
            Instruction::new(OpCode::Constant, vec![1]),
            Instruction::new(OpCode::Constant, vec![2]),
            Instruction::new(OpCode::Constant, vec![65535]),
        ]);
        assert_eq!(
            "0000 Constant 1
0003 Constant 2
0006 Constant 65535
",
            instrs.to_string()
        );
    }

    #[test]
    fn one_byte_operands_to_string() {
        let instrs = Instructions::from_iter([Instruction::new(OpCode::GetBuiltin, vec![1])]);
        assert_eq!("0000 GetBuiltin 1\n", instrs.to_string());
    }

    #[test]
    fn two_operands_to_string() {
        let instrs = Instructions::from_iter([Instruction::new(OpCode::Closure, vec![1, 1])]);
        assert_eq!("0000 Closure 1 1\n", instrs.to_string());
    }
}
