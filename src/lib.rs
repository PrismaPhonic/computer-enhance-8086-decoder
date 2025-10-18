use std::{fmt, fs};

pub mod math;
pub mod mov;

use math::{Add, RegMemoryWithRegisterToEither};
use mov::{AccToOrFromMemory, ImmediateToMemory, ImmediateToRegister, Mov, RegOrMemToOrFromReg};

/// There are 4 registers, A, B, C or D.
/// X means the full 16 bits
/// L means the lower 8 bits (right side)
/// H means the high 8 bits (left side)
pub enum Register {
    // Main registers.
    AL,
    CL,
    DL,
    BL,
    AX,
    CX,
    DX,
    BX,
    AH,
    CH,
    DH,
    BH,
    // Index registers - 16 bit only.
    SP, // Stack Pointer
    BP, // Base Pointer
    SI, // Source Index
    DI, // Destination Index
}

impl Register {
    /// Create a register from the 3-bit reg field and the W (wide) bit.
    /// wide = false -> 8-bit register
    /// wide = true  -> 16-bit register
    fn from_code(code: u8, wide: bool) -> Self {
        match (code, wide) {
            // 8-bit registers (W = 0)
            (0b000, false) => Self::AL,
            (0b001, false) => Self::CL,
            (0b010, false) => Self::DL,
            (0b011, false) => Self::BL,
            (0b100, false) => Self::AH,
            (0b101, false) => Self::CH,
            (0b110, false) => Self::DH,
            (0b111, false) => Self::BH,

            // 16-bit registers (W = 1)
            (0b000, true) => Self::AX,
            (0b001, true) => Self::CX,
            (0b010, true) => Self::DX,
            (0b011, true) => Self::BX,
            (0b100, true) => Self::SP,
            (0b101, true) => Self::BP,
            (0b110, true) => Self::SI,
            (0b111, true) => Self::DI,

            _ => unreachable!(),
        }
    }

    fn acc(wide: bool) -> Self {
        if wide { Self::AX } else { Self::AL }
    }
}

// Mod notes:
// 00 - No displacement follows (except when R/M is 110, then 16 follows, DIRECT
// ADDRESS.
// 01 - 8 bit follows (one byte)
// 10 - 16 bit follows (two bytes)
// 11 - Register mode (no displacement)
pub enum Address {
    // Mod == 00
    // Bx + Si
    // Mod == 01
    // Bx + Si + D8
    // Mod == 10
    // Bx + Si + D16
    BxSi(Option<Immediate>),

    // Mod == 00
    // Bx + Di
    // Mod == 01
    // Bx + Di + D8
    // Mod == 10
    // Bx + Di + D16
    BxDi(Option<Immediate>),

    // Mod == 00
    // Bp + Si
    // Mod == 01
    // Bp + Si + D8
    // Mod == 10
    // Bp + Si + D16
    BpSi(Option<Immediate>),

    // Mod == 00
    // Bp + Di
    // Mod == 01
    // Bp + Di + D8
    // Mod == 10
    // Bp + Di + D16
    BpDi(Option<Immediate>),

    // Mod == 00
    // Si
    // Mod == 01
    // Si + D8
    // Mod == 10
    // Si + D16
    Si(Option<Immediate>),

    // Mod == 00
    // Di
    // Mod == 01
    // Di + D8
    // Mod == 10
    // Di + D16
    Di(Option<Immediate>),

    // Mod == 00
    // Direct Address
    // The immediate in this case is the memory location, not used for address
    // calculation.
    DirectAddress(Immediate),

    // Mod == 01
    // Bp + D8
    // Mod == 10
    // Bp + D16
    Bp(Immediate),

    // Mod == 00
    // Bx
    // Mod == 01
    // Bx + D8
    // Mod == 10
    // Bx + D16
    Bx(Option<Immediate>),
}

impl Address {
    fn from_fields(rm_field: u8, mod_field: u8, lo: Option<u8>, hi: Option<u8>) -> Self {
        match (rm_field, mod_field, lo, hi) {
            // Mod field 00
            (0b000, 0b00, None, None) => Self::BxSi(None),
            (0b001, 0b00, None, None) => Self::BxDi(None),
            (0b010, 0b00, None, None) => Self::BpSi(None),
            (0b011, 0b00, None, None) => Self::BpDi(None),
            (0b100, 0b00, None, None) => Self::Si(None),
            (0b101, 0b00, None, None) => Self::Di(None),
            (0b110, 0b00, Some(lo), Some(hi)) => Self::DirectAddress(Immediate::from_full(lo, hi)),
            (0b111, 0b00, None, None) => Self::Bx(None),

            // Mod field 01 - one byte displacement.
            (0b000, 0b01, Some(lo), None) => Self::BxSi(Some(Immediate::from_lo(lo))),
            (0b001, 0b01, Some(lo), None) => Self::BxDi(Some(Immediate::from_lo(lo))),
            (0b010, 0b01, Some(lo), None) => Self::BpSi(Some(Immediate::from_lo(lo))),
            (0b011, 0b01, Some(lo), None) => Self::BpDi(Some(Immediate::from_lo(lo))),
            (0b100, 0b01, Some(lo), None) => Self::Si(Some(Immediate::from_lo(lo))),
            (0b101, 0b01, Some(lo), None) => Self::Di(Some(Immediate::from_lo(lo))),
            (0b110, 0b01, Some(lo), None) => Self::Bp(Immediate::from_lo(lo)),
            (0b111, 0b01, Some(lo), None) => Self::Bx(Some(Immediate::from_lo(lo))),

            // Mod field 10 - two byte displacement.
            (0b000, 0b10, Some(lo), Some(hi)) => Self::BxSi(Some(Immediate::from_full(lo, hi))),
            (0b001, 0b10, Some(lo), Some(hi)) => Self::BxDi(Some(Immediate::from_full(lo, hi))),
            (0b010, 0b10, Some(lo), Some(hi)) => Self::BpSi(Some(Immediate::from_full(lo, hi))),
            (0b011, 0b10, Some(lo), Some(hi)) => Self::BpDi(Some(Immediate::from_full(lo, hi))),
            (0b100, 0b10, Some(lo), Some(hi)) => Self::Si(Some(Immediate::from_full(lo, hi))),
            (0b101, 0b10, Some(lo), Some(hi)) => Self::Di(Some(Immediate::from_full(lo, hi))),
            (0b110, 0b10, Some(lo), Some(hi)) => Self::Bp(Immediate::from_full(lo, hi)),
            (0b111, 0b10, Some(lo), Some(hi)) => Self::Bx(Some(Immediate::from_full(lo, hi))),

            _ => unreachable!(),
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            // 8-bit
            Self::AL => "al",
            Self::CL => "cl",
            Self::DL => "dl",
            Self::BL => "bl",
            Self::AH => "ah",
            Self::CH => "ch",
            Self::DH => "dh",
            Self::BH => "bh",
            // 16-bit
            Self::AX => "ax",
            Self::CX => "cx",
            Self::DX => "dx",
            Self::BX => "bx",
            Self::SP => "sp",
            Self::BP => "bp",
            Self::SI => "si",
            Self::DI => "di",
        };
        f.write_str(s)
    }
}

impl fmt::Display for Address {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Helper to write "[BASE [+/- disp]]"
        let mut base_plus_disp = |base: &str, opt: &Option<Immediate>| -> fmt::Result {
            match opt {
                Some(imm) if !imm.is_zero() => {
                    let (neg, mag) = imm.sign_and_mag();
                    write!(f, "[{} {} {}]", base, if neg { '-' } else { '+' }, mag)
                }
                _ => write!(f, "[{}]", base),
            }
        };

        match self {
            // no/opt disp (two-register bases)
            Address::BxSi(opt) => base_plus_disp("bx + si", opt),
            Address::BxDi(opt) => base_plus_disp("bx + di", opt),
            Address::BpSi(opt) => base_plus_disp("bp + si", opt),
            Address::BpDi(opt) => base_plus_disp("bp + di", opt),

            // single-register bases with optional disp
            Address::Si(opt) => base_plus_disp("si", opt),
            Address::Di(opt) => base_plus_disp("di", opt),
            Address::Bx(opt) => base_plus_disp("bx", opt),

            // bp has a non-optional displacement in your type
            Address::Bp(imm) => {
                if imm.is_zero() {
                    write!(f, "[bp]")
                } else {
                    let (neg, mag) = imm.sign_and_mag();
                    write!(f, "[bp {} {}]", if neg { '-' } else { '+' }, mag)
                }
            }

            // direct address
            Address::DirectAddress(imm) => write!(f, "[{}]", imm),
        }
    }
}

pub enum Operation {
    Mov(Mov),
    Add(Add),
}

impl From<Mov> for Operation {
    fn from(value: Mov) -> Self {
        Self::Mov(value)
    }
}

impl From<Add> for Operation {
    fn from(value: Add) -> Self {
        Self::Add(value)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mov(m) => m.fmt(f),
            Self::Add(a) => a.fmt(f),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Immediate {
    Half(i8),
    Full(i16),
}

impl Immediate {
    pub fn from_lo(field: u8) -> Self {
        Self::Half(field as i8)
    }

    pub fn from_full(lo: u8, hi: u8) -> Self {
        let value = (hi as u16) << 8 | (lo as u16);
        let signed = value as i16;

        Self::Full(signed)
    }

    pub fn is_zero(&self) -> bool {
        match *self {
            Immediate::Half(v) => v == 0,
            Immediate::Full(v) => v == 0,
        }
    }

    /// Returns (is_negative, magnitude_as_u16)
    pub fn sign_and_mag(&self) -> (bool, u16) {
        match *self {
            Immediate::Half(v) => (v < 0, v.unsigned_abs() as u16),
            Immediate::Full(v) => (v < 0, v.unsigned_abs()),
        }
    }
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Immediate::Half(num) => num.fmt(f),
            Immediate::Full(num) => num.fmt(f),
        }
    }
}

pub struct Operations(Vec<Operation>);

impl fmt::Display for Operations {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, op) in self.0.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{op}")?;
        }
        Ok(())
    }
}

impl Operations {
    pub fn from_bytes(bytes: &mut Vec<u8>) -> Self {
        let mut out = vec![];
        while !bytes.is_empty() {
            let op = bytes[0];
            let decoded = if AccToOrFromMemory::opcode_matches(op)
                || ImmediateToRegister::opcode_matches(op)
                || ImmediateToMemory::opcode_matches(op)
                || RegOrMemToOrFromReg::opcode_matches(op)
            {
                Mov::try_decode(bytes).map(Operation::from)
            } else if RegMemoryWithRegisterToEither::opcode_matches(op) {
                Add::try_decode(bytes).map(Operation::from)
            } else {
                panic!("Unsupported op code");
            };

            if let Some(op) = decoded {
                out.push(op);
            }
        }

        Self(out)
    }

    pub fn try_from_file(file_path: &str) -> std::io::Result<Self> {
        let path = std::path::PathBuf::from(file_path);
        let absolute = path.canonicalize().expect("Failed to create absolute path");
        println!("path: {:?}", absolute);
        let mut bytes = fs::read(absolute)?;

        Ok(Self::from_bytes(&mut bytes))
    }
}

pub enum RegisterOrMemory {
    Reg(Register),
    Mem(Address),
}

impl From<Register> for RegisterOrMemory {
    fn from(value: Register) -> Self {
        Self::Reg(value)
    }
}

impl From<Address> for RegisterOrMemory {
    fn from(value: Address) -> Self {
        Self::Mem(value)
    }
}

impl fmt::Display for RegisterOrMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegisterOrMemory::Reg(register) => register.fmt(f),
            RegisterOrMemory::Mem(address) => address.fmt(f),
        }
    }
}
