use std::ops::Index;

pub struct Instructions {
    bytes: Vec<u8>,
    head: usize,
}

impl From<Vec<u8>> for Instructions {
    fn from(bytes: Vec<u8>) -> Self {
        Self { bytes, head: 0 }
    }
}

impl Instructions {
    pub fn take(&mut self, bytes_cnt: usize) -> Option<&[u8]> {
        if self.len() < bytes_cnt {
            return None;
        }

        let out = Some(&self.bytes[self.head..self.head + bytes_cnt]);
        self.head += bytes_cnt;
        out
    }

    pub fn peak(&self, bytes_cnt: usize) -> Option<&[u8]> {
        if self.len() < bytes_cnt {
            return None;
        }

        Some(&self.bytes[self.head..self.head + bytes_cnt])
    }

    pub fn get(&self, index: usize) -> Option<u8> {
        self.bytes.get(self.head + index).copied()
    }

    pub fn len(&self) -> usize {
        self.bytes.len() - self.head
    }

    pub fn is_empty(&self) -> bool {
        (self.bytes.len() as i16 - self.head as i16) <= 0
    }

    pub fn set_head(&mut self, new: usize) {
        self.head = new;
    }
}

impl Index<usize> for Instructions {
    type Output = u8;

    fn index(&self, idx: usize) -> &Self::Output {
        self.bytes.index(self.head + idx)
    }
}
