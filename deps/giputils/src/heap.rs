use crate::{OptionU32, grc::Grc, gvec::Gvec};

pub trait BinaryHeapCmp<T> {
    fn lge(&self, s: T, o: T) -> bool;
}

#[derive(Default)]
pub struct BinaryHeap<T: Into<u32> + Copy + PartialEq, CMP: BinaryHeapCmp<T>> {
    heap: Gvec<T>,
    pos: Gvec<OptionU32>,
    cmp: Grc<CMP>,
}

impl<T: Into<u32> + Copy + PartialEq, CMP: BinaryHeapCmp<T>> BinaryHeap<T, CMP> {
    pub fn new(cmp: Grc<CMP>) -> Self {
        Self {
            heap: Gvec::new(),
            pos: Gvec::new(),
            cmp,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.heap.len() as usize
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    #[inline]
    pub fn clear(&mut self) {
        for v in self.heap.iter().copied() {
            self.pos[v.into()] = OptionU32::NONE;
        }
        self.heap.clear();
    }

    #[inline]
    pub fn up(&mut self, v: T) {
        self.pos.reserve(v.into() + 1);
        let mut idx = match self.pos[v.into()] {
            OptionU32::NONE => return,
            idx => *idx,
        };
        while idx != 0 {
            let pidx = (idx - 1) >> 1;
            if self.cmp.lge(self.heap[pidx], v) {
                break;
            }
            self.heap[idx] = self.heap[pidx];
            *self.pos[self.heap[idx].into()] = idx;
            idx = pidx;
        }
        if self.heap[idx] != v {
            self.heap[idx] = v;
            *self.pos[v.into()] = idx;
        }
    }

    #[inline]
    pub fn down(&mut self, v: T) {
        self.pos.reserve(v.into() + 1);
        let mut idx = match self.pos[v.into()] {
            OptionU32::NONE => return,
            idx => *idx,
        };
        loop {
            let left = (idx << 1) + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child =
                if right < self.heap.len() && self.cmp.lge(self.heap[right], self.heap[left]) {
                    right
                } else {
                    left
                };
            if self.cmp.lge(v, self.heap[child]) {
                break;
            }
            self.heap[idx] = self.heap[child];
            *self.pos[self.heap[idx].into()] = idx;
            idx = child;
        }
        if self.heap[idx] != v {
            self.heap[idx] = v;
            *self.pos[v.into()] = idx;
        }
    }

    #[inline]
    pub fn push(&mut self, v: T) {
        self.pos.reserve(v.into() + 1);
        if self.pos[v.into()].is_some() {
            return;
        }
        let idx = self.heap.len();
        self.heap.push(v);
        *self.pos[v.into()] = idx;
        self.up(v);
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.heap.is_empty() {
            return None;
        }
        let value = self.heap[0];
        self.heap[0] = self.heap[self.heap.len() - 1];
        *self.pos[self.heap[0].into()] = 0;
        self.pos[value.into()] = OptionU32::NONE;
        self.heap.pop();
        if self.heap.len() > 1 {
            self.down(self.heap[0]);
        }
        Some(value)
    }

    #[inline]
    pub fn update(&mut self, v: T) {
        self.up(v);
        self.down(v);
    }

    #[inline]
    pub fn elements(&self) -> &[T] {
        &self.heap
    }
}
