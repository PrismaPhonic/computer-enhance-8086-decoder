use std::{fmt, fs};

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
}

impl From<Mov> for Operation {
    fn from(value: Mov) -> Self {
        Self::Mov(value)
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mov(m) => write!(f, "{m}"),
        }
    }
}

pub enum Mov {
    RegisterToRegister(RegOrMemToOrFromReg),
    ImmediateToRegister(ImmediateToRegister),
}

impl fmt::Display for Mov {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mov::RegisterToRegister(register_to_register) => register_to_register.fmt(f),
            Mov::ImmediateToRegister(immediate_to_register) => immediate_to_register.fmt(f),
        }
    }
}

impl From<RegOrMemToOrFromReg> for Mov {
    fn from(value: RegOrMemToOrFromReg) -> Self {
        Self::RegisterToRegister(value)
    }
}

impl From<ImmediateToRegister> for Mov {
    fn from(value: ImmediateToRegister) -> Self {
        Self::ImmediateToRegister(value)
    }
}

pub struct RegOrMemToOrFromReg {
    destination: RegisterOrMemory,
    source: RegisterOrMemory,
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

impl RegOrMemToOrFromReg {
    /// Returns true if the opcode for the byte matches a
    /// Register/memory to/from register move.
    pub fn opcode_matches(byte: u8) -> bool {
        let reg_to_reg_mask: u8 = 0b11111100;
        let reg_to_reg_id: u8 = 0b10001000;

        (byte & reg_to_reg_mask) == reg_to_reg_id
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

    fn disp_lo(bytes: &[u8], displacement: u8) -> Option<u8> {
        if displacement > 0 {
            Some(bytes[2])
        } else {
            None
        }
    }

    fn disp_hi(bytes: &[u8], displacement: u8) -> Option<u8> {
        if displacement > 1 {
            Some(bytes[3])
        } else {
            None
        }
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
                let reg_register = Register::from_code(reg_field, w_set).into();
                let rm_register = Register::from_code(rm_field, w_set).into();

                let (destination, source) = if d_set {
                    (reg_register, rm_register)
                } else {
                    (rm_register, reg_register)
                };

                Some(RegOrMemToOrFromReg {
                    destination,
                    source,
                })
            }
            // All other modes are address based.
            _ => {
                let reg_register = Register::from_code(reg_field, w_set).into();
                let rm_register = Address::from_fields(
                    rm_field,
                    mod_field,
                    Self::disp_lo(&bytes, displacement),
                    Self::disp_hi(&bytes, displacement),
                )
                .into();

                let (destination, source) = if d_set {
                    (reg_register, rm_register)
                } else {
                    (rm_register, reg_register)
                };

                Some(RegOrMemToOrFromReg {
                    destination,
                    source,
                })
            }
        }
    }
}

pub struct ImmediateToRegister {
    register: Register,
    immediate: Immediate,
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

impl ImmediateToRegister {
    /// Returns true if the opcode for the byte matches an immediate to
    /// register move.
    pub fn opcode_matches(byte: u8) -> bool {
        let immediate_to_reg_mask: u8 = 0b11110000;
        let immediate_to_reg_id: u8 = 0b10110000;

        (byte & immediate_to_reg_mask) == immediate_to_reg_id
    }

    pub fn try_decode(bytes: &mut Vec<u8>) -> Option<Self> {
        let len = bytes.len();
        if len < 2 {
            return None;
        }

        // We first check the w bit, because that will tell us how many bytes
        // this instructions will be.
        let w_set = (bytes[0] & (1 << 3)) != 0;

        if w_set {
            if len < 3 {
                return None;
            }

            // Wide set, so we need 3 bytes.
            let b: Vec<u8> = bytes.drain(0..3).collect();
            // Already the last 3 bits.
            let reg_bits = b[0] & 0b111;
            let register = Register::from_code(reg_bits, true);

            let lo = b[1];
            let hi = b[2];

            let immediate = Immediate::from_full(lo, hi);

            Some(ImmediateToRegister {
                register,
                immediate,
            })
        } else {
            // Wide not set, so we need 2 bytes.
            let b: Vec<u8> = bytes.drain(0..2).collect();

            let reg_bits = b[0] & 0b111;
            let register = Register::from_code(reg_bits, false);
            let lo = b[1];

            let immediate = Immediate::from_lo(lo);

            Some(ImmediateToRegister {
                register,
                immediate,
            })
        }
    }
}

impl fmt::Display for ImmediateToRegister {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mov {}, {}", self.register, self.immediate)
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

impl Mov {
    // TODO: Make try_decode_unchecked. We will want a process which identifies
    // what the instruction is, and then defer to us to build the instruction
    // details.
    //
    // Once that kind of a system is in place, it doesn't make sense for each
    // operation to self identify who it is.

    /// Decodes only register -> register MOVs from the 8086.
    /// Returns None for non-MOV or non reg->reg.
    pub fn try_decode(bytes: &mut Vec<u8>) -> Option<Self> {
        if bytes.len() < 2 {
            // Minimum of 2 bytes for a Mov operation.
            return None;
        }

        let op = bytes[0];

        if RegOrMemToOrFromReg::opcode_matches(op) {
            RegOrMemToOrFromReg::try_decode(bytes).map(Mov::from)
        } else if ImmediateToRegister::opcode_matches(op) {
            ImmediateToRegister::try_decode(bytes).map(Mov::from)
        } else {
            None
        }
    }
}

impl fmt::Display for RegOrMemToOrFromReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mov {}, {}", self.destination, self.source)
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
        // For now we hard code MOV as that's our only instruction.

        let mut out = vec![];
        while !bytes.is_empty() {
            // TODO: If we ever fail here, we should return an error rather than
            // continue trying to process.
            if let Some(op) = Mov::try_decode(bytes) {
                out.push(op.into())
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_multiple_movs_correctly() {
        let ops = Operations::try_from_file("many_register_mov")
            .expect("This file should exist in the repo and parse");

        let rendered = ops.to_string();

        let expected = "\
mov cx, bx
mov ch, ah
mov dx, bx
mov si, bx
mov bx, di
mov al, cl
mov ch, ch
mov bx, ax
mov bx, si
mov sp, di
mov bp, ax";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn prints_register_and_immediate_movs_in_asm_style() {
        let mut bytes = vec![
            0x89, 0xC8, 0xB1, 0x7F, 0xBA, 0x34, 0x12, 0xB8, 0x00, 0x80, 0x88, 0xC7,
        ];

        let ops = Operations::from_bytes(&mut bytes);
        let rendered = ops.to_string();

        let expected = "\
mov ax, cx
mov cl, 127
mov dx, 4660
mov ax, -32768
mov bh, al";

        assert_eq!(rendered, expected);
        assert!(bytes.is_empty());
    }

    #[test]
    fn listing_0039_passes() {
        let mut bytes = vec![
            0x8B, 0xF3, // mov si, bx
            0x8A, 0xF0, // mov dh, al
            0xB1, 0x0C, // mov cl, 12
            0xB5, 0xF4, // mov ch, -12
            0xB9, 0x0C, 0x00, // mov cx, 12
            0xB9, 0xF4, 0xFF, // mov cx, -12
            0xBA, 0x6C, 0x0F, // mov dx, 3948
            0xBA, 0x94, 0xF0, // mov dx, -3948
            0x8A, 0x00, // mov al, [bx + si]
            0x8B, 0x1B, // mov bx, [bp + di]
            0x8B, 0x56, 0x00, // mov dx, [bp]
            0x8A, 0x60, 0x04, // mov ah, [bx + si + 4]
            0x8A, 0x80, 0x87, 0x13, // mov al, [bx + si + 4999]
            0x89, 0x09, // mov [bx + di], cx
            0x88, 0x0A, // mov [bp + si], cl
            0x88, 0x6E, 0x00, // mov [bp], ch
        ];

        let ops = Operations::from_bytes(&mut bytes);
        let rendered = ops.to_string();

        let expected = "\
mov si, bx
mov dh, al
mov cl, 12
mov ch, -12
mov cx, 12
mov cx, -12
mov dx, 3948
mov dx, -3948
mov al, [bx + si]
mov bx, [bp + di]
mov dx, [bp]
mov ah, [bx + si + 4]
mov al, [bx + si + 4999]
mov [bx + di], cx
mov [bp + si], cl
mov [bp], ch";

        assert_eq!(rendered, expected);
        assert!(bytes.is_empty(), "decoder should consume all bytes");
    }

    #[test]
    fn listing_0039_passes_from_file() {
        let ops = Operations::try_from_file("listing_0039_more_movs")
            .expect("This file should exist in the repo and parse");

        let rendered = ops.to_string();

        let expected = "\
mov si, bx
mov dh, al
mov cl, 12
mov ch, -12
mov cx, 12
mov cx, -12
mov dx, 3948
mov dx, -3948
mov al, [bx + si]
mov bx, [bp + di]
mov dx, [bp]
mov ah, [bx + si + 4]
mov al, [bx + si + 4999]
mov [bx + di], cx
mov [bp + si], cl
mov [bp], ch";

        assert_eq!(rendered, expected);
    }
}
