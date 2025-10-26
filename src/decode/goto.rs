use crate::{ZF_MASK, collections::Instructions, decode::Immediate};
use std::fmt;

pub enum JumpKind {
    Je,
    Jl,
    Jle,
    Jb,
    Jbe,
    Jp,
    Jo,
    Js,
    Jnz,
    Jnl,
    Jg,
    Jnb,
    Ja,
    Jnp,
    Jno,
    Jns,
    Loop,
    Loopz,
    Loopnz,
    Jcxz,
}

impl fmt::Display for JumpKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            JumpKind::Je => "je",
            JumpKind::Jl => "jl",
            JumpKind::Jle => "jle",
            JumpKind::Jb => "jb",
            JumpKind::Jbe => "jbe",
            JumpKind::Jp => "jp",
            JumpKind::Jo => "jo",
            JumpKind::Js => "js",
            JumpKind::Jnz => "jnz",
            JumpKind::Jnl => "jnl",
            JumpKind::Jg => "jg",
            JumpKind::Jnb => "jnb",
            JumpKind::Ja => "ja",
            JumpKind::Jnp => "jnp",
            JumpKind::Jno => "jno",
            JumpKind::Jns => "jns",
            JumpKind::Loop => "loop",
            JumpKind::Loopz => "loopz",
            JumpKind::Loopnz => "loopnz",
            JumpKind::Jcxz => "jcxz",
        };
        f.write_str(s)
    }
}

pub struct Jump {
    kind: JumpKind,
    // Destination in bytes ahead or behind where we are currently.
    // Will always be 8 bit (Immediate::Half).
    pub(crate) disp: Immediate,
}

impl fmt::Display for Jump {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} short {}", self.kind, self.disp)
    }
}

impl Jump {
    pub fn classify(op: u8) -> Option<JumpKind> {
        match op {
            0b0111_0100 => Some(JumpKind::Je),
            0b0111_1100 => Some(JumpKind::Jl),
            0b0111_1110 => Some(JumpKind::Jle),
            0b0111_0010 => Some(JumpKind::Jb),
            0b0111_0110 => Some(JumpKind::Jbe),
            0b0111_1010 => Some(JumpKind::Jp),
            0b0111_0000 => Some(JumpKind::Jo),
            0b0111_1000 => Some(JumpKind::Js),
            0b0111_0101 => Some(JumpKind::Jnz),
            0b0111_1101 => Some(JumpKind::Jnl),
            0b0111_1111 => Some(JumpKind::Jg),
            0b0111_0011 => Some(JumpKind::Jnb),
            0b0111_0111 => Some(JumpKind::Ja),
            0b0111_1011 => Some(JumpKind::Jnp),
            0b0111_0001 => Some(JumpKind::Jno),
            0b0111_1001 => Some(JumpKind::Jns),

            0b1110_0010 => Some(JumpKind::Loop),
            0b1110_0001 => Some(JumpKind::Loopz),
            0b1110_0000 => Some(JumpKind::Loopnz),

            0b1110_0011 => Some(JumpKind::Jcxz),

            _ => None,
        }
    }

    pub fn try_decode(bytes: &mut Instructions) -> Option<Self> {
        let op = bytes.get(0)?;
        let kind = Self::classify(op)?;
        let bytes = bytes.take(2)?;

        Some(Jump {
            kind,
            disp: Immediate::from_lo(bytes[1]),
        })
    }

    pub fn should_jump(&self, flags_register: u16) -> bool {
        match self.kind {
            JumpKind::Jnz => {
                let zero = flags_register & ZF_MASK == ZF_MASK;
                !zero
            }

            JumpKind::Je => todo!(),
            JumpKind::Jp => todo!(),
            JumpKind::Jb => todo!(),
            JumpKind::Loopnz => todo!(),

            JumpKind::Jl => todo!(),
            JumpKind::Jle => todo!(),
            JumpKind::Jbe => todo!(),
            JumpKind::Jo => todo!(),
            JumpKind::Js => todo!(),
            JumpKind::Jnl => todo!(),
            JumpKind::Jg => todo!(),
            JumpKind::Jnb => todo!(),
            JumpKind::Ja => todo!(),
            JumpKind::Jnp => todo!(),
            JumpKind::Jno => todo!(),
            JumpKind::Jns => todo!(),
            JumpKind::Loop => todo!(),
            JumpKind::Loopz => todo!(),
            JumpKind::Jcxz => todo!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Cpu;

    #[test]
    fn jumps_disassemble_correctly() {
        let bytes = vec![
            0x75, 0x02, // jnz short +2
            0x75, 0xFC, // jnz short -4
            0x74, 0xFE, // je short -2
            0x7C, 0xFE, // jl short -2
            0xE2, 0xFE, // loop short -2
        ];

        let mut cpu = Cpu::from_instructions(bytes);
        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
jnz short 2
jnz short -4
je short -2
jl short -2
loop short -2";

        assert_eq!(rendered, expected);
    }

    #[test]
    fn listing_0041_add_sub_jnz() {
        let mut cpu = Cpu::try_from_file("listing_0041_add_sub_jnz")
            .expect("This file should exist in the repo and parse");

        let ops = cpu.generate_operations();
        let rendered = ops.to_string();

        let expected = "\
add bx, [bx + si]
add bx, [bp]
add si, 2
add bp, 2
add cx, 8
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
add byte [bx], 34
add word [bp + si + 1000], 29
add ax, [bp]
add al, [bx + si]
add ax, bx
add al, ah
add ax, 1000
add al, -30
add al, 9
sub bx, [bx + si]
sub bx, [bp]
sub si, 2
sub bp, 2
sub cx, 8
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
sub byte [bx], 34
sub word [bx + di], 29
sub ax, [bp]
sub al, [bx + si]
sub ax, bx
sub al, ah
sub ax, 1000
sub al, -30
sub al, 9
cmp bx, [bx + si]
cmp bx, [bp]
cmp si, 2
cmp bp, 2
cmp cx, 8
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
cmp byte [bx], 34
cmp word [4834], 29
cmp ax, [bp]
cmp al, [bx + si]
cmp ax, bx
cmp al, ah
cmp ax, 1000
cmp al, -30
cmp al, 9
jnz short 2
jnz short -4
jnz short -6
jnz short -4
je short -2
jl short -4
jle short -6
jb short -8
jbe short -10
jp short -12
jo short -14
js short -16
jnz short -18
jnl short -20
jg short -22
jnb short -24
ja short -26
jnp short -28
jno short -30
jns short -32
loop short -34
loopz short -36
loopnz short -38
jcxz short -40";

        assert_eq!(rendered, expected);
    }
}
