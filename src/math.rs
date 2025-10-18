use std::fmt;

use crate::{Address, Register, RegisterOrMemory};

pub enum Arithmetic {
    Add(Add),
    // Sub,
    // Cmp,
}

pub enum Add {
    RegOrMemWithRegToEither(RegMemoryWithRegisterToEither),
    // ImmToRegOrMem(ImmediateToRegisterOrMemory),
    // ImmToAcc(ImmediateToAccumulator),
}

impl Add {
    pub fn try_decode(bytes: &mut Vec<u8>) -> Option<Self> {
        if bytes.len() < 2 {
            // Minimum of 2 bytes for a Mov operation.
            return None;
        }

        let op = bytes[0];

        if RegMemoryWithRegisterToEither::opcode_matches(op) {
            RegMemoryWithRegisterToEither::try_decode(bytes).map(Add::from)
        } else {
            None
        }
    }
}

impl fmt::Display for Add {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Add::RegOrMemWithRegToEither(a) => a.fmt(f),
        }
    }
}

impl From<RegMemoryWithRegisterToEither> for Add {
    fn from(value: RegMemoryWithRegisterToEither) -> Self {
        Self::RegOrMemWithRegToEither(value)
    }
}

// One half has to be a register, and the other half can be either.
pub struct RegMemoryWithRegisterToEither {
    register: Register,
    reg_or_mem: RegisterOrMemory,
    // If true, then memory is the source.
    direction: bool,
}

impl fmt::Display for RegMemoryWithRegisterToEither {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.direction {
            write!(f, "add {}, {}", self.register, self.reg_or_mem)
        } else {
            write!(f, "add {}, {}", self.reg_or_mem, self.register)
        }
    }
}

impl RegMemoryWithRegisterToEither {
    const fn mask() -> u8 {
        0b11111100
    }

    const fn id() -> u8 {
        0b00000000
    }

    /// Returns true if the opcode for the byte matches a
    /// Register/memory to/from register move.
    pub fn opcode_matches(byte: u8) -> bool {
        (byte & Self::mask()) == Self::id()
    }

    fn d_set(bytes: &[u8]) -> bool {
        // D bit: 1=reg is dst, 0=reg is src
        (bytes[0] & (1 << 1)) != 0
    }

    fn w_set(bytes: &[u8]) -> bool {
        // W bit: 1=word (16-bit), 0=byte (8-bit)
        (bytes[0] & (1 << 0)) != 0
    }

    fn mod_field(byte: u8) -> u8 {
        byte >> 6
    }

    fn reg_field(byte: u8) -> u8 {
        (byte >> 3) & 0b111
    }

    fn rm_field(byte: u8) -> u8 {
        byte & 0b111
    }

    fn mod_reg_rm(bytes: &[u8]) -> (u8, u8, u8) {
        let byte = bytes[1];
        (
            Self::mod_field(byte),
            Self::reg_field(byte),
            Self::rm_field(byte),
        )
    }

    // Returns the displacement byte count based on the mod field, and r/m
    // field.
    fn displacement_bytes(mod_field: u8, rm_field: u8) -> u8 {
        match mod_field {
            0b00 if rm_field == 0b110 => 2,
            0b10 => 2,
            0b01 => 1,
            _ => 0,
        }
    }

    pub fn try_decode(bytes: &mut Vec<u8>) -> Option<Self> {
        if bytes.len() < 2 {
            return None;
        }

        let (mod_field, reg_field, rm_field) = Self::mod_reg_rm(bytes);

        let displacement = Self::displacement_bytes(mod_field, rm_field);

        let bytes: Vec<u8> = bytes.drain(0..2 + displacement as usize).collect();

        let w_set = Self::w_set(&bytes);
        let d_set = Self::d_set(&bytes);

        match mod_field {
            // Register to Register.
            0b11 => {
                let reg_register = Register::from_code(reg_field, w_set);
                let rm_register = Register::from_code(rm_field, w_set).into();

                Some(Self {
                    register: reg_register,
                    reg_or_mem: rm_register,
                    direction: d_set,
                })
            }
            // All other modes are address based.
            _ => {
                let reg_register = Register::from_code(reg_field, w_set);
                let rm_register = Address::from_fields(
                    rm_field,
                    mod_field,
                    (displacement >= 1).then(|| bytes[2]),
                    (displacement == 2).then(|| bytes[3]),
                )
                .into();

                Some(Self {
                    register: reg_register,
                    reg_or_mem: rm_register,
                    direction: d_set,
                })
            }
        }
    }
}

// pub struct ImmediateToRegisterOrMemory;
// pub struct ImmediateToAccumulator;
//

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn add_reg_mem_with_register_to_either() {
        let mut bytes = vec![
            0x03, 0x18, // add bx, [bx+si]
            0x03, 0x5E, 0x00, // add bx, [bp]
            0x03, 0x5E, 0x00, // add bx, [bp + 0]
            0x03, 0x4F, 0x02, // add cx, [bx + 2]
            0x02, 0x7A, 0x04, // add bh, [bp + si + 4]
            0x03, 0x7B, 0x06, // add di, [bp + di + 6]
            0x01, 0x18, // add [bx+si], bx
            0x01, 0x5E, 0x00, // add [bp], bx
            0x01, 0x5E, 0x00, // add [bp + 0], bx
            0x01, 0x4F, 0x02, // add [bx + 2], cx
            0x00, 0x7A, 0x04, // add [bp + si + 4], bh
            0x01, 0x7B, 0x06, // add [bp + di + 6], di
            0x03, 0x46, 0x00, // add ax, [bp]
            0x02, 0x00, // add al, [bx + si]
            0x03, 0xC3, // add ax, bx
            0x02, 0xC4, // add al, ah
        ];

        let ops = Operations::from_bytes(&mut bytes);
        let rendered = ops.to_string();

        let expected = "\
add bx, [bx + si]
add bx, [bp]
add bx, [bp]
add cx, [bx + 2]
add bh, [bp + si + 4]
add di, [bp + di + 6]
add [bx + si], bx
add [bp], bx
add [bp], bx
add [bx + 2], cx
add [bp + si + 4], bh
add [bp + di + 6], di
add ax, [bp]
add al, [bx + si]
add ax, bx
add al, ah";

        assert_eq!(rendered, expected);
        assert!(bytes.is_empty(), "decoder should consume all bytes");
    }
}
