use crate::decode::*;

use std::fmt;

pub enum Mov {
    RegOrMemToOrFromReg(RegOrMemToOrFromReg),
    ImmediateToRegister(ImmediateToRegister),
    ImmediateToMemory(ImmediateToMemory),
    AccToOrFromMem(AccToOrFromMemory),
    Segment(SegToOrFromRegOrMem),
}

impl fmt::Display for Mov {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mov::RegOrMemToOrFromReg(reg_or_mem_to_or_from_reg) => reg_or_mem_to_or_from_reg.fmt(f),
            Mov::ImmediateToRegister(immediate_to_register) => immediate_to_register.fmt(f),
            Mov::ImmediateToMemory(immediate_to_memory) => immediate_to_memory.fmt(f),
            Mov::AccToOrFromMem(acc_to_or_from_mem) => acc_to_or_from_mem.fmt(f),
            Mov::Segment(seg) => seg.fmt(f),
        }
    }
}

impl From<RegOrMemToOrFromReg> for Mov {
    fn from(value: RegOrMemToOrFromReg) -> Self {
        Self::RegOrMemToOrFromReg(value)
    }
}

impl From<ImmediateToRegister> for Mov {
    fn from(value: ImmediateToRegister) -> Self {
        Self::ImmediateToRegister(value)
    }
}

impl From<ImmediateToMemory> for Mov {
    fn from(value: ImmediateToMemory) -> Self {
        Self::ImmediateToMemory(value)
    }
}

impl From<AccToOrFromMemory> for Mov {
    fn from(value: AccToOrFromMemory) -> Self {
        Self::AccToOrFromMem(value)
    }
}

impl From<SegToOrFromRegOrMem> for Mov {
    fn from(value: SegToOrFromRegOrMem) -> Self {
        Self::Segment(value)
    }
}

pub struct RegOrMemToOrFromReg {
    pub destination: RegisterOrMemory,
    pub source: RegisterOrMemory,
}

impl RegOrMemToOrFromReg {
    const fn mask() -> u8 {
        0b11111100
    }

    const fn id() -> u8 {
        0b10001000
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

    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        let (mod_field, reg_field, rm_field) = Self::mod_reg_rm(bytes.peak(2)?);

        let displacement = Self::displacement_bytes(mod_field, rm_field);
        let need = 2 + displacement as usize;

        let bytes = bytes.take(need)?;

        let w_set = Self::w_set(bytes);
        let d_set = Self::d_set(bytes);

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
                    (displacement >= 1).then(|| bytes[2]),
                    (displacement == 2).then(|| bytes[3]),
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

pub struct AccToOrFromMemory {
    source: RegisterOrMemory,
    destination: RegisterOrMemory,
}

impl AccToOrFromMemory {
    const fn opcode_mask() -> u8 {
        0b11111110
    }

    const fn mem_to_acc_id() -> u8 {
        0b10100000
    }

    const fn acc_to_mem_id() -> u8 {
        0b10100010
    }

    pub fn opcode_matches(byte: u8) -> bool {
        let masked = byte & Self::opcode_mask();
        masked == Self::mem_to_acc_id() || masked == Self::acc_to_mem_id()
    }

    fn w_set(bytes: &[u8]) -> bool {
        // W bit: 1=word (16-bit), 0=byte (8-bit)
        (bytes[0] & (1 << 0)) != 0
    }

    fn mem_is_source(bytes: &[u8]) -> bool {
        let masked = bytes[0] & Self::opcode_mask();
        masked == Self::mem_to_acc_id()
    }

    fn immediate(bytes: &[u8]) -> Immediate {
        let lo = bytes[1];
        let hi = bytes[2];
        Immediate::from_full(lo, hi)
    }

    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        let bytes = bytes.take(3)?;

        let w_set = Self::w_set(&bytes);
        let immediate = Self::immediate(&bytes);

        if Self::mem_is_source(&bytes) {
            Some(AccToOrFromMemory {
                source: Address::DirectAddress(immediate).into(),
                destination: Register::acc(w_set).into(),
            })
        } else {
            Some(AccToOrFromMemory {
                source: Register::acc(w_set).into(),
                destination: Address::DirectAddress(immediate).into(),
            })
        }
    }
}

impl fmt::Display for AccToOrFromMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mov {}, {}", self.destination, self.source)
    }
}

pub struct ImmediateToRegister {
    pub register: Register,
    pub immediate: Immediate,
}

impl ImmediateToRegister {
    const fn mask() -> u8 {
        0b11110000
    }

    const fn id() -> u8 {
        0b10110000
    }

    /// Returns true if the opcode for the byte matches an immediate to
    /// register move.
    pub fn opcode_matches(byte: u8) -> bool {
        (byte & Self::mask()) == Self::id()
    }

    fn w_set(bytes: &[u8]) -> bool {
        (bytes[0] & (1 << 3)) != 0
    }

    fn reg_field(byte: u8) -> u8 {
        byte & 0b111
    }

    fn immediate(bytes: &[u8], wide: bool) -> Immediate {
        let lo = bytes[1];
        if wide {
            let hi = bytes[2];
            Immediate::from_full(lo, hi)
        } else {
            Immediate::from_lo(lo)
        }
    }

    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        // We first check the w bit, because that will tell us how many bytes
        // this instructions will be.
        let w_set = Self::w_set(bytes.peak(2)?);

        let need = if w_set { 3 } else { 2 };

        let bytes = bytes.take(need)?;

        let reg_field = Self::reg_field(bytes[0]);

        Some(ImmediateToRegister {
            register: Register::from_code(reg_field, w_set),
            immediate: Self::immediate(&bytes, w_set),
        })
    }
}

impl fmt::Display for ImmediateToRegister {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "mov {}, {}", self.register, self.immediate)
    }
}

pub struct ImmediateToMemory {
    destination: Address,
    immediate: Immediate,
}

impl fmt::Display for ImmediateToMemory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.immediate {
            Immediate::Half(num) => {
                write!(f, "mov {}, byte {}", self.destination, num)
            }
            Immediate::Full(num) => {
                write!(f, "mov {}, word {}", self.destination, num)
            }
        }
    }
}

impl ImmediateToMemory {
    const fn mask() -> u8 {
        0b1111_1110
    }

    const fn id() -> u8 {
        0b1100_0110
    }

    pub fn opcode_matches(b: u8) -> bool {
        (b & Self::mask()) == Self::id()
    }

    fn w_set(byte: u8) -> bool {
        (byte & (1 << 0)) != 0
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

    fn immediate(bytes: &[u8], displacement: u8, wide: bool) -> Immediate {
        let imm_offset = 2 + displacement as usize;
        if wide {
            Immediate::from_full(bytes[imm_offset], bytes[imm_offset + 1])
        } else {
            Immediate::from_lo(bytes[imm_offset])
        }
    }

    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        let (mod_field, reg_field, rm_field) = Self::mod_reg_rm(bytes.peak(2)?);

        if reg_field != 0 {
            return None;
        }

        if mod_field == 0b11 {
            // No assembler ever emits this, so we shouldn't handle it.
            return None;
        };

        let displacement = Self::displacement_bytes(mod_field, rm_field);

        let w_set = Self::w_set(bytes[0]);
        let need = 2 + displacement as usize + if w_set { 2 } else { 1 };

        let bytes = bytes.take(need)?;

        Some(Self {
            destination: Address::from_fields(
                rm_field,
                mod_field,
                (displacement >= 1).then(|| bytes[2]),
                (displacement == 2).then(|| bytes[3]),
            ),
            immediate: Self::immediate(&bytes, displacement, w_set),
        })
    }
}

#[derive(Clone, Copy)]
pub struct SegToOrFromRegOrMem {
    pub segment: Register,
    pub other: RegisterOrMemory,
    pub source: Source,
}

impl fmt::Display for SegToOrFromRegOrMem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.source {
            Source::RegisterOrMemory => write!(f, "mov {}, {}", self.segment, self.other),
            Source::Segment => write!(f, "mov {}, {}", self.other, self.segment),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Source {
    Segment,
    RegisterOrMemory,
}

impl SegToOrFromRegOrMem {
    pub fn classify(op: u8) -> Option<Source> {
        // Op code is the entire byte for these two
        match op {
            0b1000_1110 => Some(Source::RegisterOrMemory),
            0b1000_1100 => Some(Source::Segment),
            _ => None,
        }
    }

    fn mod_field(byte: u8) -> u8 {
        byte >> 6
    }

    fn seg_field(byte: u8) -> u8 {
        let shifted = byte >> 3;
        shifted & 0b111
    }

    fn rm_field(byte: u8) -> u8 {
        byte & 0b111
    }

    fn mod_seg_rm(bytes: &[u8]) -> (u8, u8, u8) {
        let byte = bytes[1];
        (
            Self::mod_field(byte),
            Self::seg_field(byte),
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

    pub fn try_decode(bytes: &mut Instructions, source: Source) -> Option<Self> {
        let (mod_field, seg_field, rm_field) = Self::mod_seg_rm(bytes.peak(2)?);
        let displacement = Self::displacement_bytes(mod_field, rm_field);
        let need = 2 + displacement as usize;

        let bytes = bytes.take(need)?;

        let segment = Register::seg(seg_field)?;
        match mod_field {
            0b11 => {
                // Register to register
                Some(Self {
                    segment,
                    other: Register::from_code(rm_field, true).into(),
                    source,
                })
            }
            _ => {
                // All other fields are addressed based.
                Some(Self {
                    segment,
                    other: Address::from_fields(
                        rm_field,
                        mod_field,
                        (displacement >= 1).then(|| bytes[2]),
                        (displacement == 2).then(|| bytes[3]),
                    )
                    .into(),
                    source,
                })
            }
        }
    }
}

impl Mov {
    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        if bytes.len() < 2 {
            // Minimum of 2 bytes for a Mov operation.
            return None;
        }

        let op = bytes[0];

        if RegOrMemToOrFromReg::opcode_matches(op) {
            RegOrMemToOrFromReg::try_decode(bytes).map(Mov::from)
        } else if ImmediateToRegister::opcode_matches(op) {
            ImmediateToRegister::try_decode(bytes).map(Mov::from)
        } else if AccToOrFromMemory::opcode_matches(op) {
            AccToOrFromMemory::try_decode(bytes).map(Mov::from)
        } else if ImmediateToMemory::opcode_matches(op) {
            ImmediateToMemory::try_decode(bytes).map(Mov::from)
        } else if let Some(source) = SegToOrFromRegOrMem::classify(op) {
            SegToOrFromRegOrMem::try_decode(bytes, source).map(Mov::from)
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

#[cfg(test)]
mod tests {
    use crate::Cpu;

    #[test]
    fn parses_multiple_movs_correctly() {
        let mut cpu = Cpu::try_from_file("many_register_mov")
            .expect("This file should exist in the repo and parse");
        let ops = cpu.generate_operations();

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
        let bytes = vec![
            0x89, 0xC8, 0xB1, 0x7F, 0xBA, 0x34, 0x12, 0xB8, 0x00, 0x80, 0x88, 0xC7,
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov ax, cx
mov cl, 127
mov dx, 4660
mov ax, -32768
mov bh, al";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn listing_0039_passes() {
        let bytes = vec![
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

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
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

    #[test]
    fn listing_0039_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0039_more_movs")
            .expect("This file should exist in the repo and parse");

        let ops = cpu.generate_operations();
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

    #[test]
    fn mov_signed_displacements() {
        let bytes = vec![
            0x8B, 0x41, 0xDB, // mov ax, [bx + di - 37]
            0x89, 0x8C, 0xD4, 0xFE, // mov [si - 300], cx
            0x8B, 0x57, 0xE0, // mov dx, [bx - 32]
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov ax, [bx + di - 37]
mov [si - 300], cx
mov dx, [bx - 32]";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn mov_accumulator_direct_memory_forms() {
        let bytes = vec![
            0xA1, 0xFB, 0x09, // mov ax, [2555]
            0xA1, 0x10, 0x00, // mov ax, [16]
            0xA3, 0xFA, 0x09, // mov [2554], ax
            0xA3, 0x0F, 0x00, // mov [15], ax
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov ax, [2555]
mov ax, [16]
mov [2554], ax
mov [15], ax";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn mov_accumulator_direct_memory_forms_byte_width() {
        let bytes = vec![
            0xA0, 0xFB, 0x09, // mov al, [2555]
            0xA0, 0x10, 0x00, // mov al, [16]
            0xA2, 0xFA, 0x09, // mov [2554], al
            0xA2, 0x0F, 0x00, // mov [15], al
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov al, [2555]
mov al, [16]
mov [2554], al
mov [15], al";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn mov_explicit_sizes_and_direct_address() {
        let bytes = vec![
            0xC6, 0x03, 0x07, // mov [bp + di], byte 7
            0xC7, 0x85, 0x85, 0x03, 0x5B, 0x01, // mov [di + 901], word 347
            0x8B, 0x2E, 0x05, 0x00, // mov bp, [5]
            0x8B, 0x1E, 0x82, 0x0D, // mov bx, [3458]
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov [bp + di], byte 7
mov [di + 901], word 347
mov bp, [5]
mov bx, [3458]";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn listing_0040_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0040_challenge_movs")
            .expect("This file should exist in the repo and parse");

        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov ax, [bx + di - 37]
mov [si - 300], cx
mov dx, [bx - 32]
mov [bp + di], byte 7
mov [di + 901], word 347
mov bp, [5]
mov bx, [3458]
mov ax, [2555]
mov ax, [16]
mov [2554], ax
mov [15], ax";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn mov_segment_reg_and_mem_prints() {
        let bytes = vec![
            0x8E, 0xDB, // mov ds, bx
            0x8C, 0xD8, // mov ax, ds
            0x8E, 0x52, 0x04, // mov ss, [bp + si + 4]
            0x8C, 0x07, // mov [bx], es
            0x8C, 0x5E, 0x00, // mov [bp], ds
            0x8C, 0xCB, // mov bx, cs
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
mov ds, bx
mov ax, ds
mov ss, [bp + si + 4]
mov [bx], es
mov [bp], ds
mov bx, cs";

        assert_eq!(rendered, expected);
    }
}
