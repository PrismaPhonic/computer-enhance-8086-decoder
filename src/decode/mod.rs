use std::fmt;

pub mod goto;
pub mod math;
pub mod mov;

pub use goto::Jump;
pub use math::{Add, Arithmetic, Cmp, Sub};
pub use mov::Mov;

use crate::collections::Instructions;

/// There are 4 registers, A, B, C or D.
/// X means the full 16 bits
/// L means the lower 8 bits (right side)
/// H means the high 8 bits (left side)
#[derive(Clone, Copy)]
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

    // Segment registers, 16 bit.
    CS, // Code Segment
    DS, // Data Segment
    SS, // Stack Segment
    ES, // Extra Segment
}

impl Register {
    /// Create a register from the 3-bit reg field and the W (wide) bit.
    /// wide = false -> 8-bit register
    /// wide = true  -> 16-bit register
    pub fn from_code(code: u8, wide: bool) -> Self {
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

    pub fn acc(wide: bool) -> Self {
        if wide { Self::AX } else { Self::AL }
    }

    /// Return the segment register based on the SR bits.
    /// 00 - ES
    /// 01 - CS
    /// 10 - SS
    /// 11 - DS
    /// Bit to left should always be zero, so we include that in id.
    pub fn seg(code: u8) -> Option<Self> {
        match code {
            0b000 => Some(Self::ES),
            0b001 => Some(Self::CS),
            0b010 => Some(Self::SS),
            0b011 => Some(Self::DS),
            _ => None,
        }
    }

    pub fn is_wide(&self) -> bool {
        match self {
            Self::AL
            | Self::CL
            | Self::DL
            | Self::BL
            | Self::AH
            | Self::CH
            | Self::DH
            | Self::BH => false,

            _ => true,
        }
    }
}

// Mod notes:
// 00 - No displacement follows (except when R/M is 110, then 16 follows, DIRECT
// ADDRESS.
// 01 - 8 bit follows (one byte)
// 10 - 16 bit follows (two bytes)
// 11 - Register mode (no displacement)
#[derive(Clone, Copy)]
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

    /// Returns the estimated clock cycles for the address calculation.
    pub fn effective_address_cycles(&self) -> u16 {
        match self {
            Address::DirectAddress(_) => 6,

            Address::Bx(None) | Address::Si(None) | Address::Di(None) => 5,

            Address::BpDi(None) | Address::BxSi(None) => 7,

            Address::BxDi(None) | Address::BpSi(None) => 8,

            Address::Si(Some(_)) | Address::Di(Some(_)) | Address::Bx(Some(_)) => 9,

            Address::BpDi(Some(_)) | Address::BxSi(Some(_)) => 11,

            Address::BpSi(Some(_)) | Address::BxDi(Some(_)) => 12,

            Address::Bp(imm) => {
                if imm.is_zero() {
                    5
                } else {
                    9
                }
            }
        }
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Self::AL => "al",
            Self::CL => "cl",
            Self::DL => "dl",
            Self::BL => "bl",
            Self::AH => "ah",
            Self::CH => "ch",
            Self::DH => "dh",
            Self::BH => "bh",
            Self::AX => "ax",
            Self::CX => "cx",
            Self::DX => "dx",
            Self::BX => "bx",
            Self::SP => "sp",
            Self::BP => "bp",
            Self::SI => "si",
            Self::DI => "di",
            Self::CS => "cs",
            Self::DS => "ds",
            Self::SS => "ss",
            Self::ES => "es",
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
    Math(Arithmetic),
    Jump(Jump),
}

impl Operation {
    pub fn estimated_cycles(&self) -> u16 {
        match self {
            Operation::Mov(mov) => mov.estimated_cycles(),
            Operation::Math(arithmetic) => arithmetic.estimated_cycles(),
            // TODO.
            Operation::Jump(_) => 0,
        }
    }
}

impl From<Mov> for Operation {
    fn from(value: Mov) -> Self {
        Self::Mov(value)
    }
}

impl From<Arithmetic> for Operation {
    fn from(value: Arithmetic) -> Self {
        Self::Math(value)
    }
}

impl From<Jump> for Operation {
    fn from(value: Jump) -> Self {
        Self::Jump(value)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mov(m) => m.fmt(f),
            Self::Math(a) => a.fmt(f),
            Self::Jump(j) => j.fmt(f),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Immediate {
    Half(i8),
    Full(i16),
}

impl Immediate {
    pub fn from_lo(field: u8) -> Self {
        Self::Half(field as i8)
    }

    pub fn from_lo_se(field: u8) -> Self {
        Self::Full(field as i8 as i16)
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

    pub fn is_negative(&self) -> bool {
        match *self {
            Immediate::Half(v) => v < 0,
            Immediate::Full(v) => v < 0,
        }
    }

    /// Returns (is_negative, magnitude_as_u16)
    pub fn sign_and_mag(&self) -> (bool, u16) {
        match *self {
            Immediate::Half(v) => (v < 0, v.unsigned_abs() as u16),
            Immediate::Full(v) => (v < 0, v.unsigned_abs()),
        }
    }

    pub fn is_wide(&self) -> bool {
        matches!(self, Immediate::Full(_))
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

impl std::ops::Add for Immediate {
    type Output = Immediate;

    // TODO: Deal with wrapping appropriately.
    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Immediate::Half(left), Immediate::Half(right)) => Immediate::Half(left.add(right)),
            (Immediate::Full(left), Immediate::Full(right)) => Immediate::Full(left.add(right)),

            _ => unreachable!("This should panic - be design we should not be mixing immediates"),
        }
    }
}

impl std::ops::AddAssign for Immediate {
    fn add_assign(&mut self, rhs: Self) {
        match (self, rhs) {
            (Immediate::Half(left), Immediate::Half(right)) => {
                left.add_assign(right);
            }
            (Immediate::Full(left), Immediate::Full(right)) => {
                left.add_assign(right);
            }

            _ => unreachable!("This should panic - be design we should not be mixing immediates"),
        }
    }
}

impl std::ops::Sub for Immediate {
    type Output = Immediate;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Immediate::Half(left), Immediate::Half(right)) => Immediate::Half(left.sub(right)),
            (Immediate::Full(left), Immediate::Full(right)) => Immediate::Full(left.sub(right)),

            _ => unreachable!("This should panic - be design we should not be mixing immediates"),
        }
    }
}

impl std::ops::SubAssign for Immediate {
    fn sub_assign(&mut self, rhs: Self) {
        match (self, rhs) {
            (Immediate::Half(left), Immediate::Half(right)) => {
                left.sub_assign(right);
            }
            (Immediate::Full(left), Immediate::Full(right)) => {
                left.sub_assign(right);
            }

            _ => unreachable!("This should panic - be design we should not be mixing immediates"),
        }
    }
}

impl From<Immediate> for i16 {
    fn from(value: Immediate) -> Self {
        match value {
            Immediate::Half(v) => v as i16,
            Immediate::Full(v) => v,
        }
    }
}

impl From<Immediate> for usize {
    fn from(value: Immediate) -> Self {
        match value {
            Immediate::Half(v) => v as usize,
            Immediate::Full(v) => v as usize,
        }
    }
}

impl Default for Immediate {
    fn default() -> Self {
        Self::Full(0)
    }
}

pub struct Operations(Vec<Operation>);

impl Operations {
    pub fn estimated_cycles(&self) -> u16 {
        let mut acc = 0;
        for op in self.as_ref() {
            let clock = op.estimated_cycles();
            acc += clock;
            println!("op: {op} ; Clocks: +{clock} = {acc}");
        }
        acc
    }
}

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

impl AsRef<[Operation]> for Operations {
    fn as_ref(&self) -> &[Operation] {
        self.0.as_ref()
    }
}

impl From<Vec<Operation>> for Operations {
    fn from(value: Vec<Operation>) -> Self {
        Self(value)
    }
}

#[derive(Clone, Copy)]
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

#[cfg(test)]
mod tests {
    use crate::Cpu;

    #[test]
    fn listing_0056_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0056_estimating_cycles")
            .expect("This file should exist in the repo and parse");

        let ops = cpu.generate_operations();

        let expected = 192;
        let got = ops.estimated_cycles();

        assert_eq!(got, expected);
    }
}
