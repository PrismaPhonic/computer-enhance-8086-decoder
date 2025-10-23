use decode::{
    Immediate, Mov, Operation, Operations, RegisterOrMemory,
    mov::{RegOrMemToOrFromReg, SegToOrFromRegOrMem},
};

pub mod decode;

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
}

impl Registers {
    pub fn process_operations(&mut self, ops: Operations) {
        for op in ops.as_ref() {
            self.process_operation(op);
        }
    }

    pub fn process_operation(&mut self, op: &Operation) {
        match op {
            Operation::Mov(mov) => match mov {
                Mov::RegOrMemToOrFromReg(RegOrMemToOrFromReg {
                    source: RegisterOrMemory::Reg(source),
                    destination: RegisterOrMemory::Reg(destination),
                }) => {
                    self.immediate_to_reg(*destination, self.source(*source));
                }
                Mov::Segment(SegToOrFromRegOrMem {
                    segment,
                    other: RegisterOrMemory::Reg(other),
                    source,
                }) => match source {
                    decode::mov::Source::Segment => {
                        self.immediate_to_reg(*other, self.source(*segment));
                    }
                    decode::mov::Source::RegisterOrMemory => {
                        self.immediate_to_reg(*segment, self.source(*other));
                    }
                },
                Mov::ImmediateToRegister(imm_to_reg) => {
                    self.immediate_to_reg(imm_to_reg.register, imm_to_reg.immediate);
                }
                Mov::ImmediateToMemory(_) => todo!(),
                Mov::AccToOrFromMem(_) => todo!(),
                Mov::RegOrMemToOrFromReg(_) => todo!(),
                Mov::Segment(_) => todo!(),
            },
            Operation::Math(_) => todo!(),
            Operation::Jump(_) => todo!(),
        }
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

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn mov_immediate_to_register_executes() {
        let mut bytes = vec![
            0xB8, 0x01, 0x00, // mov ax, 1
            0xBB, 0x02, 0x00, // mov bx, 2
            0xB9, 0x03, 0x00, // mov cx, 3
            0xBA, 0x04, 0x00, // mov dx, 4
            0xBC, 0x05, 0x00, // mov sp, 5
            0xBD, 0x06, 0x00, // mov bp, 6
            0xBE, 0x07, 0x00, // mov si, 7
            0xBF, 0x08, 0x00, // mov di, 8
        ];

        let ops = Operations::from_bytes(&mut bytes);
        assert!(bytes.is_empty(), "decoder should consume all bytes");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 1);
        assert_eq!(regs.bx, 2);
        assert_eq!(regs.cx, 3);
        assert_eq!(regs.dx, 4);

        assert_eq!(regs.sp, 5);
        assert_eq!(regs.bp, 6);
        assert_eq!(regs.si, 7);
        assert_eq!(regs.di, 8);
    }

    #[test]
    fn listing_0043_passes_from_file() {
        let ops = Operations::try_from_file("listing_0043_immediate_movs")
            .expect("This file should exist in the repo and parse");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 1);
        assert_eq!(regs.bx, 2);
        assert_eq!(regs.cx, 3);
        assert_eq!(regs.dx, 4);

        assert_eq!(regs.sp, 5);
        assert_eq!(regs.bp, 6);
        assert_eq!(regs.si, 7);
        assert_eq!(regs.di, 8);
    }

    #[test]
    fn mov_register_to_register_executes() {
        let mut bytes = vec![
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

        let ops = Operations::from_bytes(&mut bytes);
        assert!(bytes.is_empty(), "decoder should consume all bytes");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 4);
        assert_eq!(regs.bx, 3);
        assert_eq!(regs.cx, 2);
        assert_eq!(regs.dx, 1);

        assert_eq!(regs.sp, 1);
        assert_eq!(regs.bp, 2);
        assert_eq!(regs.si, 3);
        assert_eq!(regs.di, 4);
    }

    #[test]
    fn listing_0044_passes_from_file() {
        let ops = Operations::try_from_file("listing_0044_register_movs")
            .expect("This file should exist in the repo and parse");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 4);
        assert_eq!(regs.bx, 3);
        assert_eq!(regs.cx, 2);
        assert_eq!(regs.dx, 1);

        assert_eq!(regs.sp, 1);
        assert_eq!(regs.bp, 2);
        assert_eq!(regs.si, 3);
        assert_eq!(regs.di, 4);
    }

    #[test]
    fn mov_with_segments_and_8bit_regs_executes() {
        use crate::*;

        let mut bytes = vec![
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

        let ops = Operations::from_bytes(&mut bytes);
        assert!(bytes.is_empty(), "decoder should consume all bytes");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 0x4411);
        assert_eq!(regs.bx, 0x3344);
        assert_eq!(regs.cx, 0x6677);
        assert_eq!(regs.dx, 0x7788);

        assert_eq!(regs.ss, 0x4411);
        assert_eq!(regs.ds, 0x3344);
        assert_eq!(regs.es, 0x6677);

        assert_eq!(regs.sp, 0x4411);
        assert_eq!(regs.bp, 0x3344);
        assert_eq!(regs.si, 0x6677);
        assert_eq!(regs.di, 0x7788);
    }

    #[test]
    fn listing_0045_passes_from_file() {
        let ops = Operations::try_from_file("listing_0045_challenge_register_movs")
            .expect("This file should exist in the repo and parse");

        let mut regs = Registers::default();
        regs.process_operations(ops);

        assert_eq!(regs.ax, 0x4411);
        assert_eq!(regs.bx, 0x3344);
        assert_eq!(regs.cx, 0x6677);
        assert_eq!(regs.dx, 0x7788);

        assert_eq!(regs.ss, 0x4411);
        assert_eq!(regs.ds, 0x3344);
        assert_eq!(regs.es, 0x6677);

        assert_eq!(regs.sp, 0x4411);
        assert_eq!(regs.bp, 0x3344);
        assert_eq!(regs.si, 0x6677);
        assert_eq!(regs.di, 0x7788);
    }
}
