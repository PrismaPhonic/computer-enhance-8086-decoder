use collections::Instructions;
use decode::{
    Add, Arithmetic, Cmp, Immediate, Mov, Operation, Operations, RegisterOrMemory, Sub,
    goto::{Jump, JumpKind},
    math::{ImmediateToAccumulator, ImmediateToRegisterOrMemory, RegMemoryWithRegisterToEither},
    mov::{
        AccToOrFromMemory, ImmediateToMemory, ImmediateToRegister, RegOrMemToOrFromReg,
        SegToOrFromRegOrMem,
    },
};
use decode::{Address, math};
use std::fs;

pub mod collections;
pub mod decode;

const SF_MASK: u16 = 0b0000_0000_1000_0000;
const ZF_MASK: u16 = 0b0000_0000_0100_0000;

#[derive(Default)]
pub struct Registers {
    ax: u16,
    cx: u16,
    dx: u16,
    bx: u16,
    sp: u16,
    bp: u16,
    si: u16,
    di: u16,
    cs: u16,
    ds: u16,
    ss: u16,
    es: u16,

    // Instruction pointer register holds the offset address for next
    // instruction to be executed.
    ip: u16,

    // Register of flags.
    // For now only need to support ZF and SF
    // ZF - "zero flag" whether the last operation results in a zero.
    // SF - "sign bit" whether the result was negative or positive (intepreting
    // 2s complement)
    flags: u16,
}

impl Registers {
    fn set_flags_from_math(&mut self, math_output: decode::Immediate) {
        if math_output.is_zero() {
            // Zero means the MSB is zero which means SF should be not set.
            // In a weird way we can think of zero as being "positive" in this
            // sense.
            self.flags &= !SF_MASK;
            self.flags |= ZF_MASK;
        } else if math_output.is_negative() {
            self.flags |= SF_MASK;
            self.flags &= !ZF_MASK;
        } else {
            self.flags &= !SF_MASK;
            self.flags &= !ZF_MASK;
        }
    }

    // Like immediate to reg, but for math operations. Sets flags automatically.
    fn math_to_reg(&mut self, reg: decode::Register, math_output: decode::Immediate) {
        self.set_flags_from_math(math_output);
        self.immediate_to_reg(reg, math_output);
    }

    fn immediate_to_reg(&mut self, reg: decode::Register, imm: decode::Immediate) {
        match (reg, imm) {
            (decode::Register::AX, decode::Immediate::Full(v)) => self.ax = v as u16,
            (decode::Register::CX, decode::Immediate::Full(v)) => self.cx = v as u16,
            (decode::Register::DX, decode::Immediate::Full(v)) => self.dx = v as u16,
            (decode::Register::BX, decode::Immediate::Full(v)) => self.bx = v as u16,
            (decode::Register::SP, decode::Immediate::Full(v)) => self.sp = v as u16,
            (decode::Register::BP, decode::Immediate::Full(v)) => self.bp = v as u16,
            (decode::Register::SI, decode::Immediate::Full(v)) => self.si = v as u16,
            (decode::Register::DI, decode::Immediate::Full(v)) => self.di = v as u16,

            // These don't technically support immediate to reg, but we use
            // Immedaite as a generic holder for numbers, so this helps for
            // extensibility.
            (decode::Register::CS, decode::Immediate::Full(v)) => self.cs = v as u16,
            (decode::Register::DS, decode::Immediate::Full(v)) => self.ds = v as u16,
            (decode::Register::SS, decode::Immediate::Full(v)) => self.ss = v as u16,
            (decode::Register::ES, decode::Immediate::Full(v)) => self.es = v as u16,

            (decode::Register::AL, decode::Immediate::Half(v)) => {
                let mut bytes = self.ax.to_le_bytes();
                bytes[0] = v as u8;
                self.ax = u16::from_le_bytes(bytes);
            }
            (decode::Register::CL, decode::Immediate::Half(v)) => {
                let mut bytes = self.cx.to_le_bytes();
                bytes[0] = v as u8;
                self.cx = u16::from_le_bytes(bytes);
            }
            (decode::Register::DL, decode::Immediate::Half(v)) => {
                let mut bytes = self.dx.to_le_bytes();
                bytes[0] = v as u8;
                self.dx = u16::from_le_bytes(bytes);
            }
            (decode::Register::BL, decode::Immediate::Half(v)) => {
                let mut bytes = self.bx.to_le_bytes();
                bytes[0] = v as u8;
                self.bx = u16::from_le_bytes(bytes);
            }
            (decode::Register::AH, decode::Immediate::Half(v)) => {
                let mut bytes = self.ax.to_le_bytes();
                bytes[1] = v as u8;
                self.ax = u16::from_le_bytes(bytes);
            }
            (decode::Register::CH, decode::Immediate::Half(v)) => {
                let mut bytes = self.cx.to_le_bytes();
                bytes[1] = v as u8;
                self.cx = u16::from_le_bytes(bytes);
            }
            (decode::Register::DH, decode::Immediate::Half(v)) => {
                let mut bytes = self.dx.to_le_bytes();
                bytes[1] = v as u8;
                self.dx = u16::from_le_bytes(bytes);
            }
            (decode::Register::BH, decode::Immediate::Half(v)) => {
                let mut bytes = self.bx.to_le_bytes();
                bytes[1] = v as u8;
                self.bx = u16::from_le_bytes(bytes);
            }

            _ => unreachable!(),
        }
    }

    fn source(&self, reg: decode::Register) -> Immediate {
        match reg {
            decode::Register::AX => Immediate::Full(self.ax as i16),
            decode::Register::CX => Immediate::Full(self.cx as i16),
            decode::Register::DX => Immediate::Full(self.dx as i16),
            decode::Register::BX => Immediate::Full(self.bx as i16),
            decode::Register::SP => Immediate::Full(self.sp as i16),
            decode::Register::BP => Immediate::Full(self.bp as i16),
            decode::Register::SI => Immediate::Full(self.si as i16),
            decode::Register::DI => Immediate::Full(self.di as i16),

            decode::Register::CS => Immediate::Full(self.cs as i16),
            decode::Register::DS => Immediate::Full(self.ds as i16),
            decode::Register::SS => Immediate::Full(self.ss as i16),
            decode::Register::ES => Immediate::Full(self.es as i16),

            decode::Register::AL => {
                let bytes = self.ax.to_le_bytes();
                Immediate::Half(bytes[0] as i8)
            }
            decode::Register::CL => {
                let bytes = self.cx.to_le_bytes();
                Immediate::Half(bytes[0] as i8)
            }
            decode::Register::DL => {
                let bytes = self.dx.to_le_bytes();
                Immediate::Half(bytes[0] as i8)
            }
            decode::Register::BL => {
                let bytes = self.bx.to_le_bytes();
                Immediate::Half(bytes[0] as i8)
            }
            decode::Register::AH => {
                let bytes = self.ax.to_le_bytes();
                Immediate::Half(bytes[1] as i8)
            }
            decode::Register::CH => {
                let bytes = self.cx.to_le_bytes();
                Immediate::Half(bytes[1] as i8)
            }
            decode::Register::DH => {
                let bytes = self.dx.to_le_bytes();
                Immediate::Half(bytes[1] as i8)
            }
            decode::Register::BH => {
                let bytes = self.bx.to_le_bytes();
                Immediate::Half(bytes[1] as i8)
            }
        }
    }
}

pub struct Cpu {
    registers: Registers,
    instructions: Instructions,
    pub memory: Vec<u8>,
}

impl Cpu {
    pub fn from_instructions(instructions: Vec<u8>) -> Self {
        Self {
            registers: Registers::default(),
            instructions: instructions.into(),
            // Pre-allocate memory that is sized for the max indexing we can do
            // with a u16.
            // We ignore simulating segment registers for now.
            memory: vec![0u8; 1 << 16],
        }
    }

    pub fn try_from_file(file_path: &str) -> std::io::Result<Self> {
        let path = std::path::PathBuf::from(file_path);
        let absolute = path.canonicalize().expect("Failed to create absolute path");
        let bytes = fs::read(absolute)?;

        Ok(Self::from_instructions(bytes))
    }

    pub fn process_instructions(&mut self) {
        while !self.instructions.is_empty() {
            let op = self.next_operation();
            self.process_operation(&op);
        }
    }

    pub fn generate_operations(&mut self) -> Operations {
        let mut out = vec![];
        while !self.instructions.is_empty() {
            let op = self.next_operation();
            out.push(op);
        }
        out.into()
    }

    fn next_operation(&mut self) -> Operation {
        let start_len = self.instructions.len();

        let op = self.instructions[0];
        let decoded = if AccToOrFromMemory::opcode_matches(op)
            || ImmediateToRegister::opcode_matches(op)
            || ImmediateToMemory::opcode_matches(op)
            || RegOrMemToOrFromReg::opcode_matches(op)
        {
            Mov::try_decode(&mut self.instructions).map(Operation::from)
        } else if let Some(source) = SegToOrFromRegOrMem::classify(op) {
            SegToOrFromRegOrMem::try_decode(&mut self.instructions, source)
                .map(Mov::from)
                .map(Operation::from)
        } else if let Some(opkind) = RegMemoryWithRegisterToEither::classify(op) {
            RegMemoryWithRegisterToEither::try_decode(&mut self.instructions, opkind)
                .map(Operation::from)
        } else if let Some(opkind) = ImmediateToAccumulator::classify(op) {
            ImmediateToAccumulator::try_decode(&mut self.instructions, opkind).map(Operation::from)
        } else if math::ImmediateToRegisterOrMemory::opcode_matches(op) {
            math::ImmediateToRegisterOrMemory::try_decode(&mut self.instructions)
                .map(Operation::from)
        } else if let Some(jmp) = Jump::try_decode(&mut self.instructions) {
            Some(Operation::from(jmp))
        } else {
            panic!("Unsupported op code");
        };

        let consumed = (start_len - self.instructions.len()) as u16;
        match decoded {
            Some(opnode) => {
                // This is to more closely model how CPUs use the ip register.
                // It would probably be easier to simply let the Instruction wrapper
                // type handle setting head appropriately, but then we won't behave
                // like an 8086, and the point of this project is to simulate an
                // 8086.
                self.registers.ip += consumed;
                opnode
            }
            None => {
                // If we get here, a decoder was chosen but didn't consume bytes (truncated instr).
                // Fail fast with location + opcode.
                panic!(
                    "Truncated instruction starting at byte {:02X} (consumed {}, op {:02X})",
                    op, consumed, op
                );
            }
        }
    }

    #[inline(always)]
    fn address_calc(&self, address: Address) -> usize {
        match address {
            Address::BxSi(imm) => {
                ((self.registers.bx + self.registers.si) as i16
                    + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::BxDi(imm) => {
                ((self.registers.bx + self.registers.di) as i16
                    + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::BpSi(imm) => {
                ((self.registers.bp + self.registers.si) as i16
                    + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::BpDi(imm) => {
                ((self.registers.bp + self.registers.di) as i16
                    + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::Si(imm) => {
                (self.registers.si as i16 + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::Di(imm) => {
                (self.registers.di as i16 + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }
            Address::Bx(imm) => {
                (self.registers.bx as i16 + imm.map(|m| i16::from(m)).unwrap_or(0)) as usize
            }

            Address::Bp(imm) => (self.registers.bp as i16 + i16::from(imm)) as usize,
            Address::DirectAddress(imm) => imm.into(),
        }
    }

    fn from_memory_address(&self, address: Address, wide: bool) -> Immediate {
        self.from_memory(self.address_calc(address), wide)
    }

    fn to_memory_address(&mut self, address: Address, imm: Immediate) {
        let idx = self.address_calc(address);
        match imm {
            Immediate::Half(v) => {
                self.memory[idx] = v as u8;
            }
            Immediate::Full(v) => {
                let bytes = v.to_le_bytes();
                self.memory[idx] = bytes[0];
                self.memory[idx + 1] = bytes[1];
            }
        }
    }

    fn from_memory(&self, idx: usize, wide: bool) -> Immediate {
        if wide {
            Immediate::from_full(self.memory[idx], self.memory[idx + 1])
        } else {
            Immediate::from_lo(self.memory[idx])
        }
    }

    fn math_to_mem(&mut self, mem: Address, math_output: decode::Immediate) {
        self.registers.set_flags_from_math(math_output);
        self.to_memory_address(mem, math_output);
    }

    fn process_operation(&mut self, op: &Operation) {
        match op {
            Operation::Mov(mov) => match *mov {
                Mov::RegOrMemToOrFromReg(RegOrMemToOrFromReg {
                    source: RegisterOrMemory::Reg(source),
                    destination: RegisterOrMemory::Reg(destination),
                }) => {
                    self.registers
                        .immediate_to_reg(destination, self.registers.source(source));
                }
                Mov::RegOrMemToOrFromReg(RegOrMemToOrFromReg {
                    source: RegisterOrMemory::Mem(source),
                    destination: RegisterOrMemory::Reg(destination),
                }) => self.registers.immediate_to_reg(
                    destination,
                    self.from_memory_address(source, destination.is_wide()),
                ),
                Mov::RegOrMemToOrFromReg(RegOrMemToOrFromReg {
                    source: RegisterOrMemory::Reg(source),
                    destination: RegisterOrMemory::Mem(destination),
                }) => {
                    self.to_memory_address(destination, self.registers.source(source));
                }
                Mov::RegOrMemToOrFromReg(_) => unreachable!("Memory to Memory is impossible"),
                Mov::Segment(SegToOrFromRegOrMem {
                    segment,
                    other: RegisterOrMemory::Reg(other),
                    source,
                }) => match source {
                    decode::mov::Source::Segment => {
                        self.registers
                            .immediate_to_reg(other, self.registers.source(segment));
                    }
                    decode::mov::Source::RegisterOrMemory => {
                        self.registers
                            .immediate_to_reg(segment, self.registers.source(other));
                    }
                },
                Mov::Segment(SegToOrFromRegOrMem {
                    segment,
                    other: RegisterOrMemory::Mem(other),
                    source,
                }) => match source {
                    decode::mov::Source::Segment => {
                        self.to_memory_address(other, self.registers.source(segment));
                    }
                    decode::mov::Source::RegisterOrMemory => {
                        self.registers
                            .immediate_to_reg(segment, self.from_memory_address(other, true));
                    }
                },
                Mov::ImmediateToRegister(imm_to_reg) => {
                    self.registers
                        .immediate_to_reg(imm_to_reg.register, imm_to_reg.immediate);
                }
                Mov::ImmediateToMemory(ImmediateToMemory {
                    destination,
                    immediate,
                }) => {
                    self.to_memory_address(destination, immediate);
                }
                Mov::AccToOrFromMem(AccToOrFromMemory {
                    source: RegisterOrMemory::Reg(acc),
                    destination: RegisterOrMemory::Mem(dest),
                }) => {
                    self.to_memory_address(dest, self.registers.source(acc));
                }
                Mov::AccToOrFromMem(AccToOrFromMemory {
                    source: RegisterOrMemory::Mem(source),
                    destination: RegisterOrMemory::Reg(acc),
                }) => {
                    self.registers
                        .immediate_to_reg(acc, self.from_memory_address(source, acc.is_wide()));
                }
                Mov::AccToOrFromMem(_) => unreachable!("no mem to mem for acc"),
            },
            Operation::Math(math) => match math {
                // 1. Do basic computation
                // 2. See if the result is zero
                // 3. If not see if result is pos or neg.
                //
                // There almost certainly is a cleaner way to do this.
                // If our "registers" were variants that held the inner type,
                // then we could directly impl AddAssign.
                Arithmetic::Add(add) => match *add {
                    Add::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Reg(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.registers.source(other);
                            let mut left = self.registers.source(register);
                            left += right;
                            self.registers.math_to_reg(register, left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.registers.source(other);
                            left += right;
                            self.registers.math_to_reg(other, left);
                        }
                    }
                    Add::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Mem(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.from_memory_address(other, register.is_wide());
                            let mut left = self.registers.source(register);
                            left += right;
                            self.registers.math_to_reg(register, left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.from_memory_address(other, register.is_wide());
                            left += right;
                            self.math_to_mem(other, left);
                        }
                    }
                    Add::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Reg(dst),
                        imm,
                        ..
                    })
                    | Add::ImmToAcc(ImmediateToAccumulator {
                        destination: dst,
                        immediate: imm,
                    }) => {
                        let mut left = self.registers.source(dst);
                        left += imm;
                        self.registers.math_to_reg(dst, left);
                    }
                    Add::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Mem(dst),
                        imm,
                        ..
                    }) => {
                        let mut left = self.from_memory_address(dst, imm.is_wide());
                        left += imm;
                        self.math_to_mem(dst, left);
                    }
                },
                Arithmetic::Sub(sub) => match *sub {
                    Sub::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Reg(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.registers.source(other);
                            let mut left = self.registers.source(register);
                            left -= right;
                            self.registers.math_to_reg(register, left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.registers.source(other);
                            left -= right;
                            self.registers.math_to_reg(other, left);
                        }
                    }
                    Sub::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Mem(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.from_memory_address(other, register.is_wide());
                            let mut left = self.registers.source(register);
                            left -= right;
                            self.registers.math_to_reg(register, left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.from_memory_address(other, register.is_wide());
                            left -= right;
                            self.math_to_mem(other, left);
                        }
                    }
                    Sub::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Reg(dst),
                        imm,
                        ..
                    })
                    | Sub::ImmToAcc(ImmediateToAccumulator {
                        destination: dst,
                        immediate: imm,
                    }) => {
                        let mut left = self.registers.source(dst);
                        left -= imm;
                        self.registers.math_to_reg(dst, left);
                    }
                    Sub::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Mem(dst),
                        imm,
                        ..
                    }) => {
                        let mut left = self.from_memory_address(dst, imm.is_wide());
                        left -= imm;
                        self.math_to_mem(dst, left);
                    }
                },
                Arithmetic::Cmp(cmp) => match *cmp {
                    Cmp::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Reg(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.registers.source(other);
                            let mut left = self.registers.source(register);
                            left -= right;
                            self.registers.set_flags_from_math(left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.registers.source(other);
                            left -= right;
                            self.registers.set_flags_from_math(left);
                        }
                    }
                    Cmp::RegOrMemWithRegToEither(RegMemoryWithRegisterToEither {
                        register,
                        reg_or_mem: RegisterOrMemory::Mem(other),
                        direction,
                    }) => {
                        // "Source" is always right hand side - but we'll use
                        // source to get left hand side to, as in adds it's both
                        // a source and destination. Behaves like +=
                        if direction {
                            let right = self.from_memory_address(other, register.is_wide());
                            let mut left = self.registers.source(register);
                            left -= right;
                            self.registers.set_flags_from_math(left);
                        } else {
                            let right = self.registers.source(register);
                            let mut left = self.from_memory_address(other, register.is_wide());
                            left -= right;
                            self.registers.set_flags_from_math(left);
                        }
                    }
                    Cmp::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Reg(dst),
                        imm,
                        ..
                    })
                    | Cmp::ImmToAcc(ImmediateToAccumulator {
                        destination: dst,
                        immediate: imm,
                    }) => {
                        let mut left = self.registers.source(dst);
                        left -= imm;
                        self.registers.set_flags_from_math(left);
                    }
                    Cmp::ImmToRegOrMem(ImmediateToRegisterOrMemory {
                        dst: RegisterOrMemory::Mem(dst),
                        imm,
                        ..
                    }) => {
                        let mut left = self.from_memory_address(dst, imm.is_wide());
                        left -= imm;
                        self.registers.set_flags_from_math(left);
                    }
                },
            },
            Operation::Jump(jmp) => {
                match jmp.kind {
                    JumpKind::Jnz => {
                        let zero = self.registers.flags & ZF_MASK == ZF_MASK;
                        if !zero {
                            let next_ip = (self.registers.ip as i16 + i16::from(jmp.disp)) as u16;
                            self.registers.ip = next_ip;
                            self.instructions.set_head(next_ip as usize);
                        }
                    }
                    // Can't determine from flags_register alone, need cx.
                    JumpKind::Loop => {
                        self.registers.cx -= 1;
                        if self.registers.cx != 0 {
                            let next_ip = (self.registers.ip as i16 + i16::from(jmp.disp)) as u16;
                            self.registers.ip = next_ip;
                            self.instructions.set_head(next_ip as usize);
                        }
                    }

                    _ => todo!("Implement rest of jumps"),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn mov_immediate_to_register_executes() {
        let bytes = vec![
            0xB8, 0x01, 0x00, // mov ax, 1
            0xBB, 0x02, 0x00, // mov bx, 2
            0xB9, 0x03, 0x00, // mov cx, 3
            0xBA, 0x04, 0x00, // mov dx, 4
            0xBC, 0x05, 0x00, // mov sp, 5
            0xBD, 0x06, 0x00, // mov bp, 6
            0xBE, 0x07, 0x00, // mov si, 7
            0xBF, 0x08, 0x00, // mov di, 8
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 1);
        assert_eq!(cpu.registers.bx, 2);
        assert_eq!(cpu.registers.cx, 3);
        assert_eq!(cpu.registers.dx, 4);

        assert_eq!(cpu.registers.sp, 5);
        assert_eq!(cpu.registers.bp, 6);
        assert_eq!(cpu.registers.si, 7);
        assert_eq!(cpu.registers.di, 8);
    }

    #[test]
    fn listing_0043_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0043_immediate_movs")
            .expect("This file should exist in the repo and parse");

        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 1);
        assert_eq!(cpu.registers.bx, 2);
        assert_eq!(cpu.registers.cx, 3);
        assert_eq!(cpu.registers.dx, 4);

        assert_eq!(cpu.registers.sp, 5);
        assert_eq!(cpu.registers.bp, 6);
        assert_eq!(cpu.registers.si, 7);
        assert_eq!(cpu.registers.di, 8);
    }

    #[test]
    fn mov_register_to_register_executes() {
        let bytes = vec![
            0xB8, 0x01, 0x00, // mov ax, 1
            0xBB, 0x02, 0x00, // mov bx, 2
            0xB9, 0x03, 0x00, // mov cx, 3
            0xBA, 0x04, 0x00, // mov dx, 4
            0x8B, 0xE0, // mov sp, ax
            0x8B, 0xEB, // mov bp, bx
            0x8B, 0xF1, // mov si, cx
            0x8B, 0xFA, // mov di, dx
            0x8B, 0xD4, // mov dx, sp
            0x8B, 0xCD, // mov cx, bp
            0x8B, 0xDE, // mov bx, si
            0x8B, 0xC7, // mov ax, di
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 4);
        assert_eq!(cpu.registers.bx, 3);
        assert_eq!(cpu.registers.cx, 2);
        assert_eq!(cpu.registers.dx, 1);

        assert_eq!(cpu.registers.sp, 1);
        assert_eq!(cpu.registers.bp, 2);
        assert_eq!(cpu.registers.si, 3);
        assert_eq!(cpu.registers.di, 4);
    }

    #[test]
    fn listing_0044_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0044_register_movs")
            .expect("This file should exist in the repo and parse");

        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 4);
        assert_eq!(cpu.registers.bx, 3);
        assert_eq!(cpu.registers.cx, 2);
        assert_eq!(cpu.registers.dx, 1);

        assert_eq!(cpu.registers.sp, 1);
        assert_eq!(cpu.registers.bp, 2);
        assert_eq!(cpu.registers.si, 3);
        assert_eq!(cpu.registers.di, 4);
    }

    #[test]
    fn mov_with_segments_and_8bit_regs_executes() {
        use crate::*;

        let bytes = vec![
            0xB8, 0x22, 0x22, // mov ax, 0x2222
            0xBB, 0x44, 0x44, // mov bx, 0x4444
            0xB9, 0x66, 0x66, // mov cx, 0x6666
            0xBA, 0x88, 0x88, // mov dx, 0x8888
            0x8E, 0xD0, // mov ss, ax
            0x8E, 0xDB, // mov ds, bx
            0x8E, 0xC1, // mov es, cx
            0xB0, 0x11, // mov al, 0x11
            0xB7, 0x33, // mov bh, 0x33
            0xB1, 0x55, // mov cl, 0x55
            0xB6, 0x77, // mov dh, 0x77
            0x8A, 0xE3, // mov ah, bl
            0x8A, 0xCE, // mov cl, dh
            0x8E, 0xD0, // mov ss, ax
            0x8E, 0xDB, // mov ds, bx
            0x8E, 0xC1, // mov es, cx
            0x8C, 0xD4, // mov sp, ss
            0x8C, 0xDD, // mov bp, ds
            0x8C, 0xC6, // mov si, es
            0x8B, 0xFA, // mov di, dx
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 0x4411);
        assert_eq!(cpu.registers.bx, 0x3344);
        assert_eq!(cpu.registers.cx, 0x6677);
        assert_eq!(cpu.registers.dx, 0x7788);

        assert_eq!(cpu.registers.ss, 0x4411);
        assert_eq!(cpu.registers.ds, 0x3344);
        assert_eq!(cpu.registers.es, 0x6677);

        assert_eq!(cpu.registers.sp, 0x4411);
        assert_eq!(cpu.registers.bp, 0x3344);
        assert_eq!(cpu.registers.si, 0x6677);
        assert_eq!(cpu.registers.di, 0x7788);
    }

    #[test]
    fn listing_0045_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0045_challenge_register_movs")
            .expect("This file should exist in the repo and parse");

        cpu.process_instructions();

        assert_eq!(cpu.registers.ax, 0x4411);
        assert_eq!(cpu.registers.bx, 0x3344);
        assert_eq!(cpu.registers.cx, 0x6677);
        assert_eq!(cpu.registers.dx, 0x7788);

        assert_eq!(cpu.registers.ss, 0x4411);
        assert_eq!(cpu.registers.ds, 0x3344);
        assert_eq!(cpu.registers.es, 0x6677);

        assert_eq!(cpu.registers.sp, 0x4411);
        assert_eq!(cpu.registers.bp, 0x3344);
        assert_eq!(cpu.registers.si, 0x6677);
        assert_eq!(cpu.registers.di, 0x7788);
    }

    #[test]
    fn math_reg_only_executes_and_sets_flags() {
        use crate::*;

        // Program:
        // mov bx, -4093
        // mov cx, 3841
        // sub bx, cx
        //
        // mov sp, 998
        // mov bp, 999
        // cmp bp, sp
        //
        // add bp, 1027
        // sub bp, 2026

        let bytes = vec![
            0xBB, 0x03, 0xF0, 0xB9, 0x01, 0x0F, 0x2B, 0xD9, 0xBC, 0xE6, 0x03, 0xBD, 0xE7, 0x03,
            0x3B, 0xEC, 0x81, 0xC5, 0x03, 0x04, 0x81, 0xED, 0xEA, 0x07,
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0xE102);
        assert_eq!(cpu.registers.cx, 0x0F01);

        assert_eq!(cpu.registers.sp, 0x03E6);
        assert_eq!(cpu.registers.bp, 0x0000);

        assert_eq!(cpu.registers.flags & ZF_MASK, ZF_MASK, "ZF should be set");
        assert_eq!(cpu.registers.flags & SF_MASK, 0, "SF should be clear");
    }

    #[test]
    fn listing_0046_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0046_add_sub_cmp")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0xE102);
        assert_eq!(cpu.registers.cx, 0x0F01);

        assert_eq!(cpu.registers.sp, 0x03E6);
        assert_eq!(cpu.registers.bp, 0x0000);

        assert_eq!(cpu.registers.flags & ZF_MASK, ZF_MASK, "ZF should be set");
        assert_eq!(cpu.registers.flags & SF_MASK, 0, "SF should be clear");
    }

    #[test]
    fn ip_and_state_for_mov_add_mov_sub_sequence() {
        use crate::*;

        let bytes = vec![
            0xB9, 0xC8, 0x00, // mov cx, 200
            0x8B, 0xD9, // mov bx, cx
            0x81, 0xC1, 0xE8, 0x03, // add cx, 1000
            0xBB, 0xD0, 0x07, // mov bx, 2000
            0x2B, 0xCB, // sub cx, bx
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0x07D0);
        assert_eq!(cpu.registers.cx, 0xFCE0);

        // IP should equal total bytes consumed: 3 + 2 + 4 + 3 + 2 = 14.
        assert_eq!(cpu.registers.ip, 14);

        // Flags: result (-800) is negative, not zero.
        assert_ne!(cpu.registers.flags & SF_MASK, 0, "SF should be set");
        assert_eq!(cpu.registers.flags & ZF_MASK, 0, "ZF should be clear");
    }

    #[test]
    fn listing_0048_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0048_ip_register")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0x07D0);
        assert_eq!(cpu.registers.cx, 0xFCE0);

        // IP should equal total bytes consumed: 3 + 2 + 4 + 3 + 2 = 14.
        assert_eq!(cpu.registers.ip, 14);

        // Flags: result (-800) is negative, not zero.
        assert_ne!(cpu.registers.flags & SF_MASK, 0, "SF should be set");
        assert_eq!(cpu.registers.flags & ZF_MASK, 0, "ZF should be clear");
    }

    #[test]
    fn jnz_loop_adds_until_cx_zero() {
        use crate::*;

        // Program:
        // mov cx, 3
        // mov bx, 1000
        // loop_start:
        //   add bx, 10
        //   sub cx, 1
        //   jnz loop_start
        let bytes = vec![
            0xB9, 0x03, 0x00, // mov cx, 3
            0xBB, 0xE8, 0x03, // mov bx, 1000
            0x83, 0xC3, 0x0A, // add bx, 10
            0x83, 0xE9, 0x01, // sub cx, 1
            0x75, 0xF8, // jnz -8
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0x0406);
        assert_eq!(cpu.registers.cx, 0x0000);

        // IP should be total length (no final jump taken): 3 + 3 + 3 + 3 + 2 = 14
        assert_eq!(cpu.registers.ip, 14);

        // Flags after final sub (cx=0): ZF=1, SF=0
        assert_ne!(cpu.registers.flags & ZF_MASK, 0, "ZF should be set");
        assert_eq!(cpu.registers.flags & SF_MASK, 0, "SF should be clear");
    }

    #[test]
    fn listing_0049_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0049_conditional_jumps")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 0x0406);
        assert_eq!(cpu.registers.cx, 0x0000);

        // IP should be total length (no final jump taken): 3 + 3 + 3 + 3 + 2 = 14
        assert_eq!(cpu.registers.ip, 14);

        // Flags after final sub (cx=0): ZF=1, SF=0
        assert_ne!(cpu.registers.flags & ZF_MASK, 0, "ZF should be set");
        assert_eq!(cpu.registers.flags & SF_MASK, 0, "SF should be clear");
    }

    #[test]
    fn mem_moves_and_indexed_store_then_loads() {
        use crate::*;

        // Program:
        // mov word [1000], 1
        // mov word [1002], 2
        // mov word [1004], 3
        // mov word [1006], 4
        // mov bx, 1000
        // mov word [bx + 4], 10    ; overwrites [1004]
        // mov bx, word [1000]
        // mov cx, word [1002]
        // mov dx, word [1004]
        // mov bp, word [1006]
        let bytes = vec![
            0xC7, 0x06, 0xE8, 0x03, 0x01, 0x00, 0xC7, 0x06, 0xEA, 0x03, 0x02, 0x00, 0xC7, 0x06,
            0xEC, 0x03, 0x03, 0x00, 0xC7, 0x06, 0xEE, 0x03, 0x04, 0x00, 0xBB, 0xE8, 0x03, 0xC7,
            0x47, 0x04, 0x0A, 0x00, 0x8B, 0x1E, 0xE8, 0x03, 0x8B, 0x0E, 0xEA, 0x03, 0x8B, 0x16,
            0xEC, 0x03, 0x8B, 0x2E, 0xEE, 0x03,
        ];

        let mut cpu = Cpu::from_instructions(bytes);

        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 1);
        assert_eq!(cpu.registers.cx, 2);
        assert_eq!(cpu.registers.dx, 10);
        assert_eq!(cpu.registers.bp, 4);
        assert_eq!(cpu.registers.ip, 48);
    }

    #[test]
    fn listing_0051_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0051_memory_mov")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 1);
        assert_eq!(cpu.registers.cx, 2);
        assert_eq!(cpu.registers.dx, 10);
        assert_eq!(cpu.registers.bp, 4);
        assert_eq!(cpu.registers.ip, 48);
    }

    #[test]
    fn loop_store_and_sum_executes() {
        use crate::*;

        // Program:
        // mov dx, 6
        // mov bp, 1000
        // mov si, 0
        // init_loop_start:
        //   mov word [bp + si], si
        //   add si, 2
        //   cmp si, dx
        //   jnz init_loop_start
        // mov bx, 0
        // mov si, 0
        // add_loop_start:
        //   mov cx, word [bp + si]
        //   add bx, cx
        //   add si, 2
        //   cmp si, dx
        //   jnz add_loop_start

        let bytes = vec![
            0xBA, 0x06, 0x00, 0xBD, 0xE8, 0x03, 0xBE, 0x00, 0x00, 0x89, 0x32, 0x83, 0xC6, 0x02,
            0x39, 0xD6, 0x75, 0xF7, 0xBB, 0x00, 0x00, 0xBE, 0x00, 0x00, 0x8B, 0x0A, 0x01, 0xCB,
            0x83, 0xC6, 0x02, 0x39, 0xD6, 0x75, 0xF5,
        ];

        let mut cpu = Cpu::from_instructions(bytes);

        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 6);
        assert_eq!(cpu.registers.cx, 4);
        assert_eq!(cpu.registers.dx, 6);
        assert_eq!(cpu.registers.si, 6);
        assert_eq!(cpu.registers.bp, 1000);
        assert_eq!(cpu.registers.ip, 35);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // ZF set
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // SF clear
    }

    #[test]
    fn listing_0052_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0052_memory_add_loop")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 6);
        assert_eq!(cpu.registers.cx, 4);
        assert_eq!(cpu.registers.dx, 6);
        assert_eq!(cpu.registers.si, 6);
        assert_eq!(cpu.registers.bp, 1000);
        assert_eq!(cpu.registers.ip, 35);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // ZF set
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // SF clear
    }

    #[test]
    fn two_phase_init_then_sum_with_backward_jumps() {
        use crate::*;

        // Program:
        // mov dx, 6
        // mov bp, 1000
        // mov si, 0
        // init_loop_start:
        //   mov word [bp + si], si
        //   add si, 2
        //   cmp si, dx
        //   jnz init_loop_start
        //
        // mov bx, 0
        // mov si, dx
        // sub bp, 2
        // add_loop_start:
        //   add bx, word [bp + si]
        //   sub si, 2
        //   jnz add_loop_start

        let bytes = vec![
            0xBA, 0x06, 0x00, 0xBD, 0xE8, 0x03, 0xBE, 0x00, 0x00, 0x89, 0x32, 0x83, 0xC6, 0x02,
            0x39, 0xD6, 0x75, 0xF7, 0xBB, 0x00, 0x00, 0x89, 0xD6, 0x83, 0xED, 0x02, 0x03, 0x1A,
            0x83, 0xEE, 0x02, 0x75, 0xF9,
        ];

        let mut cpu = Cpu::from_instructions(bytes);

        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 6);
        assert_eq!(cpu.registers.si, 0);
        assert_eq!(cpu.registers.dx, 6);
        assert_eq!(cpu.registers.bp, 998);
        assert_eq!(cpu.registers.ip, 33);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // ZF set
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // SF clear
    }

    #[test]
    fn listing_0053_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0053_add_loop_challenge")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 6);
        assert_eq!(cpu.registers.si, 0);
        assert_eq!(cpu.registers.dx, 6);
        assert_eq!(cpu.registers.bp, 998);
        assert_eq!(cpu.registers.ip, 33);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // ZF set
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // SF clear
    }

    #[test]
    fn image_fill_like_nested_loops() {
        // Program:
        // mov bp, 64*4
        // mov dx, 0
        // y_loop_start:
        //   mov cx, 0
        // x_loop_start:
        //   mov word [bp + 0], cx ; R
        //   mov word [bp + 2], dx ; B
        //   mov byte [bp + 3], 255 ; A
        //   add bp, 4
        //   add cx, 1
        //   cmp cx, 64
        //   jnz x_loop_start
        // add dx, 1
        // cmp dx, 64
        // jnz y_loop_start

        let bytes = vec![
            0xBD, 0x00, 0x01, 0xBA, 0x00, 0x00, 0xB9, 0x00, 0x00, 0x89, 0x4E, 0x00, 0x89, 0x56,
            0x02, 0xC6, 0x46, 0x03, 0xFF, 0x83, 0xC5, 0x04, 0x83, 0xC1, 0x01, 0x83, 0xF9, 0x40,
            0x75, 0xEB, 0x83, 0xC2, 0x01, 0x83, 0xFA, 0x40, 0x75, 0xE0,
        ];

        let mut cpu = Cpu::from_instructions(bytes);

        cpu.process_instructions();

        assert_eq!(cpu.registers.cx, 64);
        assert_eq!(cpu.registers.dx, 64);
        assert_eq!(cpu.registers.bp, 16640);
        assert_eq!(cpu.registers.ip, 38);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // Z
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // S clear
    }

    #[test]
    fn listing_0054_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0054_draw_rectangle")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.cx, 64);
        assert_eq!(cpu.registers.dx, 64);
        assert_eq!(cpu.registers.bp, 16640);
        assert_eq!(cpu.registers.ip, 38);

        assert_ne!(cpu.registers.flags & ZF_MASK, 0); // Z
        assert_eq!(cpu.registers.flags & SF_MASK, 0); // S clear
    }

    #[test]
    fn image_fill_with_loops_and_outline() {
        // Program:
        // mov bp, 64*4
        // mov dx, 64
        // y_loop_start:
        //   mov cx, 64
        // x_loop_start:
        //   mov byte [bp + 0], cl
        //   mov byte [bp + 1], 0
        //   mov byte [bp + 2], dl
        //   mov byte [bp + 3], 255
        //   add bp, 4
        //   loop x_loop_start
        //   sub dx, 1
        //   jnz y_loop_start
        //
        // mov bp, 64*4 + 4*64 + 4
        // mov bx, bp
        // mov cx, 62
        // outline_loop_start:
        //   mov byte [bp + 1], 255
        //   mov byte [0x3D01], 255
        //   mov byte [bx + 1], 255
        //   mov byte [bx + (61*4 + 1)], 255
        //   add bp, 4
        //   add bx, 4*64
        //   loop outline_loop_start

        let bytes = vec![
            0xBD, 0x00, 0x01, // mov bp, 256
            0xBA, 0x40, 0x00, // mov dx, 64
            0xB9, 0x40, 0x00, // mov cx, 64
            0x88, 0x4E, 0x00, // mov [bp+0], cl
            0xC6, 0x46, 0x01, 0x00, // mov byte [bp+1], 0
            0x88, 0x56, 0x02, // mov [bp+2], dl
            0xC6, 0x46, 0x03, 0xFF, // mov byte [bp+3], 255
            0x83, 0xC5, 0x04, // add bp, 4
            0xE2, 0xED, // loop x_loop_start
            0x83, 0xEA, 0x01, // sub dx, 1
            0x75, 0xE5, // jnz y_loop_start
            0xBD, 0x04, 0x02, // mov bp, 516
            0x8B, 0xDD, // mov bx, bp
            0xB9, 0x3E, 0x00, // mov cx, 62
            0xC6, 0x46, 0x01, 0xFF, // mov byte [bp+1], 255
            0xC6, 0x06, 0x01, 0x3D, 0xFF, // mov byte [0x3D01], 255
            0xC6, 0x47, 0x01, 0xFF, // mov byte [bx+1], 255
            0xC6, 0x87, 0xF5, 0x00, 0xFF, // mov byte [bx+245], 255
            0x83, 0xC5, 0x04, // add bp, 4
            0x81, 0xC3, 0x00, 0x01, // add bx, 256
            0xE2, 0xE5, // loop outline_loop_start
        ];

        let path = std::path::PathBuf::from("listing_0055_challenge_rectangle");
        let absolute = path.canonicalize().expect("Failed to create absolute path");
        let bytes_from_file = fs::read(absolute).unwrap();

        for i in 0..bytes_from_file.len() {
            let expected = bytes_from_file[i];
            let got = bytes[i];
            if got != expected {
                println!("Index: {i}; Expected {:x}; Got: {:x}", expected, got);
            }
        }

        let mut cpu = Cpu::from_instructions(bytes);
        cpu.process_instructions();

        assert_eq!(cpu.registers.bx, 16388);
        assert_eq!(cpu.registers.bp, 764);
        assert_eq!(cpu.registers.ip, 68);
    }

    #[test]
    fn listing_0055_passes_from_file() {
        let mut cpu = Cpu::try_from_file("listing_0055_challenge_rectangle")
            .expect("This file should exist in the repo and parse");
        cpu.process_instructions();

        assert_eq!(cpu.registers.ip, 68);
        assert_eq!(cpu.registers.bp, 764);
        assert_eq!(cpu.registers.bx, 16388);
    }
}
