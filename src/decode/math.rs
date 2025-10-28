use std::fmt;

use crate::{
    collections::Instructions,
    decode::{Address, Immediate, Register, RegisterOrMemory},
};

pub enum Arithmetic {
    Add(Add),
    Sub(Sub),
    Cmp(Cmp),
}

impl Arithmetic {
    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        if bytes.len() < 2 {
            // Minimum of 2 bytes for a Mov operation.
            return None;
        }

        let op = bytes[0];

        if ImmediateToRegisterOrMemory::opcode_matches(op) {
            ImmediateToRegisterOrMemory::try_decode(bytes)
        } else if let Some(opkind) = RegMemoryWithRegisterToEither::classify(op) {
            RegMemoryWithRegisterToEither::try_decode(bytes, opkind)
        } else if let Some(opkind) = ImmediateToAccumulator::classify(op) {
            ImmediateToAccumulator::try_decode(bytes, opkind)
        } else {
            None
        }
    }

    pub fn estimated_cycles(&self) -> u16 {
        match self {
            Arithmetic::Add(add) => add.estimated_cycles(),
            // TODO: Left as zero for now because this will break early testing
            // if these are actually todo!() macros
            Arithmetic::Sub(_) => 0,
            Arithmetic::Cmp(_) => 0,
        }
    }
}

impl fmt::Display for Arithmetic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Arithmetic::Add(add) => add.fmt(f),
            Arithmetic::Sub(sub) => sub.fmt(f),
            Arithmetic::Cmp(cmp) => cmp.fmt(f),
        }
    }
}

impl From<Add> for Arithmetic {
    fn from(value: Add) -> Self {
        Self::Add(value)
    }
}

impl From<Sub> for Arithmetic {
    fn from(value: Sub) -> Self {
        Self::Sub(value)
    }
}

impl From<Cmp> for Arithmetic {
    fn from(value: Cmp) -> Self {
        Self::Cmp(value)
    }
}

#[derive(Clone, Copy)]
pub enum Add {
    RegOrMemWithRegToEither(RegMemoryWithRegisterToEither),
    ImmToRegOrMem(ImmediateToRegisterOrMemory),
    ImmToAcc(ImmediateToAccumulator),
}

impl Add {
    pub fn estimated_cycles(&self) -> u16 {
        match self {
            Add::RegOrMemWithRegToEither(inner) => {
                match (inner.reg_or_mem, inner.direction) {
                    (RegisterOrMemory::Reg(_), _) => 3,
                    (RegisterOrMemory::Mem(addr), true) => {
                        // Memory is the source.
                        9 + addr.effective_address_cycles()
                    }
                    (RegisterOrMemory::Mem(addr), false) => {
                        // Reg is the source.
                        16 + addr.effective_address_cycles()
                    }
                }
            }
            Add::ImmToRegOrMem(inner) => match inner.dst {
                RegisterOrMemory::Reg(_) => 4,
                RegisterOrMemory::Mem(addr) => 17 + addr.effective_address_cycles(),
            },
            Add::ImmToAcc(_) => 4,
        }
    }
}

#[derive(Clone, Copy)]
pub enum Sub {
    RegOrMemWithRegToEither(RegMemoryWithRegisterToEither),
    ImmToRegOrMem(ImmediateToRegisterOrMemory),
    ImmToAcc(ImmediateToAccumulator),
}

#[derive(Clone, Copy)]
pub enum Cmp {
    RegOrMemWithRegToEither(RegMemoryWithRegisterToEither),
    ImmToRegOrMem(ImmediateToRegisterOrMemory),
    ImmToAcc(ImmediateToAccumulator),
}

impl fmt::Display for Add {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Add::RegOrMemWithRegToEither(a) => write!(f, "add {}", a),
            Add::ImmToRegOrMem(i) => write!(f, "add {}", i),
            Add::ImmToAcc(acc) => write!(f, "add {}", acc),
        }
    }
}

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sub::RegOrMemWithRegToEither(a) => write!(f, "sub {}", a),
            Sub::ImmToRegOrMem(i) => write!(f, "sub {}", i),
            Sub::ImmToAcc(acc) => write!(f, "sub {}", acc),
        }
    }
}

impl fmt::Display for Cmp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Cmp::RegOrMemWithRegToEither(a) => write!(f, "cmp {}", a),
            Cmp::ImmToRegOrMem(i) => write!(f, "cmp {}", i),
            Cmp::ImmToAcc(acc) => write!(f, "cmp {}", acc),
        }
    }
}

impl From<RegMemoryWithRegisterToEither> for Add {
    fn from(value: RegMemoryWithRegisterToEither) -> Self {
        Self::RegOrMemWithRegToEither(value)
    }
}

// One half has to be a register, and the other half can be either.
#[derive(Clone, Copy)]
pub struct RegMemoryWithRegisterToEither {
    pub register: Register,
    pub reg_or_mem: RegisterOrMemory,
    // If true, then memory is the source.
    pub direction: bool,
}

impl fmt::Display for RegMemoryWithRegisterToEither {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.direction {
            write!(f, "{}, {}", self.register, self.reg_or_mem)
        } else {
            write!(f, "{}, {}", self.reg_or_mem, self.register)
        }
    }
}

impl RegMemoryWithRegisterToEither {
    const fn mask() -> u8 {
        0b11111100
    }

    pub fn classify(op: u8) -> Option<AluOp> {
        match op & Self::mask() {
            0b0000_0000 => Some(AluOp::Add), // 000000dw: 00,01,02,03
            0b0010_1000 => Some(AluOp::Sub), // 001010dw: 28,29,2A,2B
            0b0011_1000 => Some(AluOp::Cmp), // 001110dw: 38,39,3A,3B
            _ => None,
        }
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
    fn displacement_bytes(mod_field: u8, rm_field: u8) -> usize {
        match mod_field {
            0b00 if rm_field == 0b110 => 2,
            0b10 => 2,
            0b01 => 1,
            _ => 0,
        }
    }

    pub fn try_decode(bytes: &mut Instructions, opkind: AluOp) -> Option<Arithmetic> {
        let (mod_field, reg_field, rm_field) = Self::mod_reg_rm(bytes.peak(2)?);

        let displacement = Self::displacement_bytes(mod_field, rm_field);
        let need = 2 + displacement;

        let bytes = bytes.take(need)?;

        let w_set = Self::w_set(bytes);
        let d_set = Self::d_set(bytes);

        let (register, reg_or_mem) = match mod_field {
            // Register to Register.
            0b11 => {
                let reg = Register::from_code(reg_field, w_set);
                let rm = Register::from_code(rm_field, w_set).into();

                (reg, rm)
            }
            // All other modes are address based.
            _ => {
                let reg = Register::from_code(reg_field, w_set);
                let rm = Address::from_fields(
                    rm_field,
                    mod_field,
                    (displacement >= 1).then(|| bytes[2]),
                    (displacement == 2).then(|| bytes[3]),
                )
                .into();

                (reg, rm)
            }
        };

        let node = RegMemoryWithRegisterToEither {
            register,
            reg_or_mem,
            direction: d_set,
        };

        Some(match opkind {
            AluOp::Add => Arithmetic::Add(Add::RegOrMemWithRegToEither(node)),
            AluOp::Sub => Arithmetic::Sub(Sub::RegOrMemWithRegToEither(node)),
            AluOp::Cmp => Arithmetic::Cmp(Cmp::RegOrMemWithRegToEither(node)),
        })
    }
}

/// Which ALU op the /reg field requested (we only care about these three for now).
#[derive(Clone, Copy, Debug)]
pub enum AluOp {
    Add,
    Sub,
    Cmp,
}

impl AluOp {
    fn from_id_field(reg: u8) -> Option<Self> {
        match reg {
            0b000 => Some(AluOp::Add),
            0b101 => Some(AluOp::Sub),
            0b111 => Some(AluOp::Cmp),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
pub struct ImmediateToRegisterOrMemory {
    pub dst: RegisterOrMemory,
    pub imm: Immediate,
    pub wide: bool,
}

impl ImmediateToRegisterOrMemory {
    const fn mask() -> u8 {
        0b1111_1100
    }

    const fn id() -> u8 {
        0b1000_0000
    }

    fn s_set(bytes: &[u8]) -> bool {
        (bytes[0] & (1 << 1)) != 0
    }

    fn w_set(bytes: &[u8]) -> bool {
        (bytes[0] & (1 << 0)) != 0
    }

    /// Returns true if the opcode for the byte matches a
    /// Register/memory to/from register move.
    pub fn opcode_matches(byte: u8) -> bool {
        (byte & Self::mask()) == Self::id()
    }

    fn mod_field(byte: u8) -> u8 {
        byte >> 6
    }

    fn id_field(byte: u8) -> u8 {
        (byte >> 3) & 0b111
    }

    fn rm_field(byte: u8) -> u8 {
        byte & 0b111
    }

    fn mod_id_rm(bytes: &[u8]) -> (u8, u8, u8) {
        let byte = bytes[1];
        (
            Self::mod_field(byte),
            Self::id_field(byte),
            Self::rm_field(byte),
        )
    }

    fn displacement_bytes(mod_field: u8, rm_field: u8) -> u8 {
        match mod_field {
            0b00 if rm_field == 0b110 => 2,
            0b10 => 2,
            0b01 => 1,
            _ => 0,
        }
    }

    fn immediate(bytes: &[u8], displacement: u8, wide: bool, se: bool) -> Immediate {
        let imm_offset = 2 + displacement as usize;

        if !wide {
            Immediate::from_lo(bytes[imm_offset])
        } else if se {
            Immediate::from_lo_se(bytes[imm_offset])
        } else {
            Immediate::from_full(bytes[imm_offset], bytes[imm_offset + 1])
        }
    }

    pub fn try_decode(bytes: &mut Instructions) -> Option<Arithmetic> {
        let peak = bytes.peak(3)?;

        let (mod_field, id_field, rm_field) = Self::mod_id_rm(peak);
        let displacement = Self::displacement_bytes(mod_field, rm_field);

        let wide = Self::w_set(peak);
        let uses_se = Self::s_set(peak);

        // immediate length
        let imm_len = if !wide || uses_se { 1 } else { 2 };

        let need = 2 + displacement as usize + imm_len;

        let bytes = bytes.take(need)?;

        let opkind = AluOp::from_id_field(id_field)?;

        // destination
        let dst = if mod_field == 0b11 {
            // Register to register.
            Register::from_code(rm_field, wide).into()
        } else {
            // All other modes are address based
            let lo = (displacement >= 1).then(|| bytes[2]);
            let hi = (displacement == 2).then(|| bytes[3]);
            Address::from_fields(rm_field, mod_field, lo, hi).into()
        };

        let s = Self {
            dst,
            imm: Self::immediate(&bytes, displacement, wide, uses_se),
            wide,
        };

        let res = match opkind {
            AluOp::Add => Arithmetic::Add(Add::ImmToRegOrMem(s)),
            AluOp::Sub => Arithmetic::Sub(Sub::ImmToRegOrMem(s)),
            AluOp::Cmp => Arithmetic::Cmp(Cmp::ImmToRegOrMem(s)),
        };

        Some(res)
    }
}

impl fmt::Display for ImmediateToRegisterOrMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.dst {
            RegisterOrMemory::Reg(r) => write!(f, "{}, {}", r, self.imm),
            RegisterOrMemory::Mem(m) => {
                if self.wide {
                    write!(f, "word {}, {}", m, self.imm)
                } else {
                    write!(f, "byte {}, {}", m, self.imm)
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct ImmediateToAccumulator {
    pub destination: Register,
    pub immediate: Immediate,
}

impl fmt::Display for ImmediateToAccumulator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}, {}", self.destination, self.immediate)
    }
}

impl ImmediateToAccumulator {
    const fn mask() -> u8 {
        0b1111_1110
    }

    pub fn classify(op: u8) -> Option<AluOp> {
        match op & Self::mask() {
            0b0000_0100 => Some(AluOp::Add),
            0b0010_1100 => Some(AluOp::Sub),
            0b0011_1100 => Some(AluOp::Cmp),
            _ => None,
        }
    }

    fn w_set(byte: u8) -> bool {
        (byte & (1 << 0)) != 0
    }

    fn immediate(bytes: &[u8], wide: bool) -> Immediate {
        if wide {
            Immediate::from_full(bytes[1], bytes[2])
        } else {
            Immediate::from_lo(bytes[1])
        }
    }

    pub fn try_decode(bytes: &mut Instructions, op_type: AluOp) -> Option<Arithmetic> {
        let w_set = Self::w_set(bytes.get(0)?);
        let need = 1 + if w_set { 2 } else { 1 };

        let bytes = bytes.take(need)?;

        let destination = if w_set { Register::AX } else { Register::AL };
        let immediate = Self::immediate(&bytes, w_set);
        let node = Self {
            destination,
            immediate,
        };

        Some(match op_type {
            AluOp::Add => Arithmetic::Add(Add::ImmToAcc(node)),
            AluOp::Sub => Arithmetic::Sub(Sub::ImmToAcc(node)),
            AluOp::Cmp => Arithmetic::Cmp(Cmp::ImmToAcc(node)),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::Cpu;

    #[test]
    fn add_reg_mem_with_register_to_either() {
        let bytes = vec![
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

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
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
    }

    #[test]
    fn arithmetic_immediate_to_reg_or_mem_via_operations() {
        let bytes = vec![
            // -------- ADD --------
            0x83, 0xC6, 0x02, // add si, 2
            0x83, 0xC5, 0x02, // add bp, 2
            0x83, 0xC1, 0x08, // add cx, 8
            0x80, 0x07, 0x22, // add byte [bx], 34
            0x81, 0x82, 0xE8, 0x03, 0x1D, 0x00, // add word [bp + si + 1000], 29
            // -------- SUB --------
            0x83, 0xEE, 0x02, // sub si, 2
            0x83, 0xED, 0x02, // sub bp, 2
            0x83, 0xE9, 0x08, // sub cx, 8
            0x80, 0x2F, 0x22, // sub byte [bx], 34
            0x81, 0x29, 0x1D, 0x00, // sub word [bx + di], 29
            // -------- CMP --------
            0x83, 0xFE, 0x02, // cmp si, 2
            0x83, 0xFD, 0x02, // cmp bp, 2
            0x83, 0xF9, 0x08, // cmp cx, 8
            0x80, 0x3F, 0x22, // cmp byte [bx], 34
            0x81, 0x3E, 0xE2, 0x12, 0x1D, 0x00, // cmp word [4834], 29  (direct addr = 0x12E2)
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
add si, 2
add bp, 2
add cx, 8
add byte [bx], 34
add word [bp + si + 1000], 29
sub si, 2
sub bp, 2
sub cx, 8
sub byte [bx], 34
sub word [bx + di], 29
cmp si, 2
cmp bp, 2
cmp cx, 8
cmp byte [bx], 34
cmp word [4834], 29";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn sub_and_cmp_regmem_with_reg_to_either_via_operations() {
        let bytes = vec![
            // -------- SUB --------
            0x2B, 0x18, // sub bx, [bx+si]            (d=1,w=1)
            0x2B, 0x5E, 0x00, // sub bx, [bp]
            0x2B, 0x5E, 0x00, // sub bx, [bp + 0]
            0x2B, 0x4F, 0x02, // sub cx, [bx + 2]
            0x2A, 0x7A, 0x04, // sub bh, [bp + si + 4]      (d=1,w=0)
            0x2B, 0x7B, 0x06, // sub di, [bp + di + 6]
            0x29, 0x18, // sub [bx+si], bx            (d=0,w=1)
            0x29, 0x5E, 0x00, // sub [bp], bx
            0x29, 0x5E, 0x00, // sub [bp + 0], bx
            0x29, 0x4F, 0x02, // sub [bx + 2], cx
            0x28, 0x7A, 0x04, // sub [bp + si + 4], bh      (d=0,w=0)
            0x29, 0x7B, 0x06, // sub [bp + di + 6], di
            0x2B, 0x46, 0x00, // sub ax, [bp]
            0x2A, 0x00, // sub al, [bx + si]
            0x2B, 0xC3, // sub ax, bx
            0x2A, 0xC4, // sub al, ah
            // -------- CMP --------
            0x3B, 0x18, // cmp bx, [bx+si]            (d=1,w=1)
            0x3B, 0x5E, 0x00, // cmp bx, [bp]
            0x3B, 0x5E, 0x00, // cmp bx, [bp + 0]
            0x3B, 0x4F, 0x02, // cmp cx, [bx + 2]
            0x3A, 0x7A, 0x04, // cmp bh, [bp + si + 4]      (d=1,w=0)
            0x3B, 0x7B, 0x06, // cmp di, [bp + di + 6]
            0x39, 0x18, // cmp [bx+si], bx            (d=0,w=1)
            0x39, 0x5E, 0x00, // cmp [bp], bx
            0x39, 0x5E, 0x00, // cmp [bp + 0], bx
            0x39, 0x4F, 0x02, // cmp [bx + 2], cx
            0x38, 0x7A, 0x04, // cmp [bp + si + 4], bh      (d=0,w=0)
            0x39, 0x7B, 0x06, // cmp [bp + di + 6], di
            0x3B, 0x46, 0x00, // cmp ax, [bp]
            0x3A, 0x00, // cmp al, [bx + si]
            0x3B, 0xC3, // cmp ax, bx
            0x3A, 0xC4, // cmp al, ah
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
sub bx, [bx + si]
sub bx, [bp]
sub bx, [bp]
sub cx, [bx + 2]
sub bh, [bp + si + 4]
sub di, [bp + di + 6]
sub [bx + si], bx
sub [bp], bx
sub [bp], bx
sub [bx + 2], cx
sub [bp + si + 4], bh
sub [bp + di + 6], di
sub ax, [bp]
sub al, [bx + si]
sub ax, bx
sub al, ah
cmp bx, [bx + si]
cmp bx, [bp]
cmp bx, [bp]
cmp cx, [bx + 2]
cmp bh, [bp + si + 4]
cmp di, [bp + di + 6]
cmp [bx + si], bx
cmp [bp], bx
cmp [bp], bx
cmp [bx + 2], cx
cmp [bp + si + 4], bh
cmp [bp + di + 6], di
cmp ax, [bp]
cmp al, [bx + si]
cmp ax, bx
cmp al, ah";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn immediate_to_accumulator_add_sub_cmp() {
        let bytes = vec![
            0x05, 0xE8, 0x03, 0x04, 0xE2, 0x04, 0x09, 0x2D, 0xE8, 0x03, 0x2C, 0xE2, 0x2C, 0x09,
            0x3D, 0xE8, 0x03, 0x3C, 0xE2, 0x3C, 0x09,
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
add ax, 1000
add al, -30
add al, 9
sub ax, 1000
sub al, -30
sub al, 9
cmp ax, 1000
cmp al, -30
cmp al, 9";

        assert_eq!(rendered, expected);
    }
}
