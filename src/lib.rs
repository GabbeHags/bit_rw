#![deny(unsafe_code)]
use std::fmt::{Binary, Debug, Formatter};

#[derive(Debug)]
pub enum Error {
    IndexOutOfRange,
}

macro_rules! cast_to_bit {
    ($bit:ident) => {{
        match $bit {
            0 => crate::Bit::Zero,
            1 => crate::Bit::One,
            _ => panic!("Could not cast {} because it is not a 1 or 0.", $bit),
        }
    }};
}
macro_rules! cast_from_bit {
    ($bit:ident) => {{
        match $bit {
            crate::Bit::Zero => 0,
            crate::Bit::One => 1,
        }
    }};
}

#[derive(Debug, Copy, Clone)]
pub enum Bit {
    Zero,
    One,
}

impl Bit {
    pub fn invert(&self) -> Self {
        match self {
            Self::Zero => Self::One,
            Self::One => Self::Zero,
        }
    }
}

impl PartialEq<Self> for Bit {
    fn eq(&self, other: &Self) -> bool {
        cast_from_bit!(self) == cast_from_bit!(other)
    }
}

impl Eq for Bit {}

impl From<u8> for Bit {
    fn from(bit: u8) -> Self {
        cast_to_bit!(bit)
    }
}

impl From<&u8> for Bit {
    fn from(bit: &u8) -> Self {
        cast_to_bit!(bit)
    }
}

impl From<Bit> for u8 {
    fn from(bit: Bit) -> Self {
        cast_from_bit!(bit)
    }
}

impl From<&Bit> for u8 {
    fn from(bit: &Bit) -> Self {
        cast_from_bit!(bit)
    }
}

#[derive(Default)]
pub struct Bits8 {
    bits: u8,
}

impl Bits8 {
    pub fn new(bits: u8) -> Self {
        Self { bits }
    }

    pub fn push_back(&mut self, bit: Bit) {
        self.bits <<= 1_u8;
        if matches!(bit, Bit::One) {
            self.bits |= 1_u8;
        }
    }

    pub fn push_front(&mut self, bit: Bit) {
        self.bits >>= 1_u8;
        if matches!(bit, Bit::One) {
            self.bits |= 1 << 7;
        }
    }

    pub fn get_and_set<F: FnOnce(Bit) -> Bit>(&mut self, index: u8, f: F) -> Result<(), Error> {
        let bit = self.get(index)?;
        self.set_unchecked(index, f(bit));
        Ok(())
    }

    pub fn get_and_set_unchecked<F: FnOnce(Bit) -> Bit>(&mut self, index: u8, f: F) {
        self.set_unchecked(index, f(self.get_unchecked(index)));
    }

    pub fn set(&mut self, index: u8, bit: Bit) -> Result<(), Error> {
        if (0..8).contains(&index) {
            self.set_unchecked(index, bit);
            Ok(())
        } else {
            Err(Error::IndexOutOfRange)
        }
    }

    pub fn set_unchecked(&mut self, index: u8, bit: Bit) {
        match bit {
            Bit::Zero => self.bits &= !(1 << index),
            Bit::One => self.bits |= 1 << index,
        }
    }

    pub fn get(&self, index: u8) -> Result<Bit, Error> {
        if (0..8).contains(&index) {
            Ok(self.get_unchecked(index))
        } else {
            Err(Error::IndexOutOfRange)
        }
    }

    pub fn get_unchecked(&self, index: u8) -> Bit {
        if self.bits & 1 << index == 0 {
            Bit::Zero
        } else {
            Bit::One
        }
    }
}

impl Binary for Bits8 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:08b}", &self.bits))
    }
}

impl Debug for Bits8 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str("Bits8 { bits: ")?;
        f.write_fmt(format_args!("{:08b}", &self.bits))?;
        f.write_str(" }")
    }
}

impl From<u8> for Bits8 {
    fn from(bits: u8) -> Self {
        Self::new(bits)
    }
}

#[cfg(test)]
mod tests {
    use crate::Bit::*;
    use crate::*;

    #[test]
    fn get_and_set() {
        todo!()
    }
    #[test]
    fn get_and_set_unchecked() {
        todo!()
    }

    #[test]
    fn push_back_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.push_back(One);
        assert_eq!(b.bits, 0b1);
        b.push_back(One);
        assert_eq!(b.bits, 0b11);
        b.push_back(One);
        assert_eq!(b.bits, 0b111);
        b.push_back(One);
        assert_eq!(b.bits, 0b1111);
        b.push_back(One);
        assert_eq!(b.bits, 0b11111);
        b.push_back(One);
        assert_eq!(b.bits, 0b111111);
        b.push_back(One);
        assert_eq!(b.bits, 0b1111111);
        b.push_back(One);
        assert_eq!(b.bits, 0b11111111);
    }
    #[test]
    fn push_back_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
        b.push_back(Zero);
        assert_eq!(b.bits, 0);
    }
    #[test]
    fn push_back_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.push_back(One);
        assert_eq!(b.bits, 0b1);
        b.push_back(Zero);
        assert_eq!(b.bits, 0b10);
        b.push_back(One);
        assert_eq!(b.bits, 0b101);
        b.push_back(Zero);
        assert_eq!(b.bits, 0b1010);
        b.push_back(One);
        assert_eq!(b.bits, 0b1_0101);
        b.push_back(Zero);
        assert_eq!(b.bits, 0b1010_10);
        b.push_back(One);
        assert_eq!(b.bits, 0b101_0101);
        b.push_back(Zero);
        assert_eq!(b.bits, 0b1010_1010);
    }

    #[test]
    fn push_front_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.push_front(One);
        assert_eq!(b.bits, 0b1000_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1100_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1110_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1111_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1111_1000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1111_1100);
        b.push_front(One);
        assert_eq!(b.bits, 0b1111_1110);
        b.push_front(One);
        assert_eq!(b.bits, 0b1111_1111);
    }

    #[test]
    fn push_front_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
        b.push_front(Zero);
        assert_eq!(b.bits, 0);
    }

    #[test]
    fn push_front_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.push_front(One);
        assert_eq!(b.bits, 0b1000_0000);
        b.push_front(Zero);
        assert_eq!(b.bits, 0b0100_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1010_0000);
        b.push_front(Zero);
        assert_eq!(b.bits, 0b0101_0000);
        b.push_front(One);
        assert_eq!(b.bits, 0b1010_1000);
        b.push_front(Zero);
        assert_eq!(b.bits, 0b0101_0100);
        b.push_front(One);
        assert_eq!(b.bits, 0b1010_1010);
        b.push_front(Zero);
        assert_eq!(b.bits, 0b0101_0101);
    }

    #[test]
    fn get_out_of_range() {
        let b = Bits8::default();
        assert!(matches!(b.get(8).unwrap_err(), Error::IndexOutOfRange));
    }

    #[test]
    fn get_zeros_and_ones() {
        let b = Bits8::new(0b0101_0101);
        for i in 0..8 {
            let bit_u8: u8 = b.get(i).unwrap().into();
            if i % 2 == 0 {
                assert_eq!(bit_u8, 1);
            } else {
                assert_eq!(bit_u8, 0);
            }
        }
    }

    #[test]
    fn get_ones() {
        let b = Bits8::new(0b1111_1111);
        for i in 0..8 {
            let bit_u8: u8 = b.get(i).unwrap().into();
            assert_eq!(bit_u8, 1);
        }
    }
    #[test]
    fn get_zeros() {
        let b = Bits8::new(0b0);
        for i in 0..8 {
            let bit_u8: u8 = b.get(i).unwrap().into();
            assert_eq!(bit_u8, 0);
        }
    }

    #[test]
    #[should_panic]
    fn get_unchecked_panic() {
        Bits8::default().get_unchecked(8);
    }

    #[test]
    fn get_unchecked_zeros_and_ones() {
        let b = Bits8::new(0b0101_0101);
        for i in 0..8 {
            let bit_u8: u8 = b.get_unchecked(i).into();
            if i % 2 == 0 {
                assert_eq!(bit_u8, 1);
            } else {
                assert_eq!(bit_u8, 0);
            }
        }
    }

    #[test]
    fn get_unchecked_ones() {
        let b = Bits8::new(0b1111_1111);
        for i in 0..8 {
            let bit_u8: u8 = b.get_unchecked(i).into();
            assert_eq!(bit_u8, 1);
        }
    }
    #[test]
    fn get_unchecked_zeros() {
        let b = Bits8::new(0b0);
        for i in 0..8 {
            let bit_u8: u8 = b.get_unchecked(i).into();
            assert_eq!(bit_u8, 0);
        }
    }

    #[test]
    fn set_out_of_range() {
        assert!(matches!(
            Bits8::default().set(8, One).unwrap_err(),
            Error::IndexOutOfRange
        ));
    }

    #[test]
    fn set_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set(0, One).unwrap();
        assert_eq!(b.bits, 0b0000_0001);
        b.set(4, One).unwrap();
        assert_eq!(b.bits, 0b0001_0001);
        b.set(7, One).unwrap();
        assert_eq!(b.bits, 0b1001_0001);
        b.set(1, One).unwrap();
        assert_eq!(b.bits, 0b1001_0011);
        b.set(0, One).unwrap();
        assert_eq!(b.bits, 0b1001_0011);
        b.set(2, One).unwrap();
        assert_eq!(b.bits, 0b1001_0111);
        b.set(5, One).unwrap();
        assert_eq!(b.bits, 0b1011_0111);
        b.set(3, One).unwrap();
        assert_eq!(b.bits, 0b1011_1111);
        b.set(6, One).unwrap();
        assert_eq!(b.bits, 0b1111_1111);
    }

    #[test]
    fn set_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set(0, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(4, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(7, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(1, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(0, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(2, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(5, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(3, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
        b.set(6, Zero).unwrap();
        assert_eq!(b.bits, 0b0);
    }

    #[test]
    fn set_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set(0, One).unwrap();
        assert_eq!(b.bits, 0b0000_0001);
        b.set(4, Zero).unwrap();
        assert_eq!(b.bits, 0b0000_0001);
        b.set(7, One).unwrap();
        assert_eq!(b.bits, 0b1000_0001);
        b.set(1, Zero).unwrap();
        assert_eq!(b.bits, 0b1000_0001);
        b.set(0, One).unwrap();
        assert_eq!(b.bits, 0b1000_0001);
        b.set(2, Zero).unwrap();
        assert_eq!(b.bits, 0b1000_0001);
        b.set(5, One).unwrap();
        assert_eq!(b.bits, 0b1010_0001);
        b.set(3, Zero).unwrap();
        assert_eq!(b.bits, 0b1010_0001);
        b.set(6, One).unwrap();
        assert_eq!(b.bits, 0b1110_0001);

        b.set(0, Zero).unwrap();
        assert_eq!(b.bits, 0b1110_0000);
        b.set(4, One).unwrap();
        assert_eq!(b.bits, 0b1111_0000);
        b.set(7, Zero).unwrap();
        assert_eq!(b.bits, 0b0111_0000);
        b.set(1, One).unwrap();
        assert_eq!(b.bits, 0b0111_0010);
        b.set(0, Zero).unwrap();
        assert_eq!(b.bits, 0b0111_0010);
        b.set(2, One).unwrap();
        assert_eq!(b.bits, 0b0111_0110);
        b.set(5, Zero).unwrap();
        assert_eq!(b.bits, 0b0101_0110);
        b.set(3, One).unwrap();
        assert_eq!(b.bits, 0b0101_1110);
        b.set(6, Zero).unwrap();
        assert_eq!(b.bits, 0b0001_1110);
    }

    #[test]
    #[should_panic]
    fn set_unchecked_panic() {
        Bits8::default().set_unchecked(8, One);
    }

    #[test]
    fn set_unchecked_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(0, One);
        assert_eq!(b.bits, 0b0000_0001);
        b.set_unchecked(4, One);
        assert_eq!(b.bits, 0b0001_0001);
        b.set_unchecked(7, One);
        assert_eq!(b.bits, 0b1001_0001);
        b.set_unchecked(1, One);
        assert_eq!(b.bits, 0b1001_0011);
        b.set_unchecked(0, One);
        assert_eq!(b.bits, 0b1001_0011);
        b.set_unchecked(2, One);
        assert_eq!(b.bits, 0b1001_0111);
        b.set_unchecked(5, One);
        assert_eq!(b.bits, 0b1011_0111);
        b.set_unchecked(3, One);
        assert_eq!(b.bits, 0b1011_1111);
        b.set_unchecked(6, One);
        assert_eq!(b.bits, 0b1111_1111);
    }

    #[test]
    fn set_unchecked_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(0, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(4, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(7, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(1, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(0, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(2, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(5, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(3, Zero);
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(6, Zero);
        assert_eq!(b.bits, 0b0);
    }

    #[test]
    fn set_unchecked_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b.bits, 0b0);
        b.set_unchecked(0, One);
        assert_eq!(b.bits, 0b0000_0001);
        b.set_unchecked(4, Zero);
        assert_eq!(b.bits, 0b0000_0001);
        b.set_unchecked(7, One);
        assert_eq!(b.bits, 0b1000_0001);
        b.set_unchecked(1, Zero);
        assert_eq!(b.bits, 0b1000_0001);
        b.set_unchecked(0, One);
        assert_eq!(b.bits, 0b1000_0001);
        b.set_unchecked(2, Zero);
        assert_eq!(b.bits, 0b1000_0001);
        b.set_unchecked(5, One);
        assert_eq!(b.bits, 0b1010_0001);
        b.set_unchecked(3, Zero);
        assert_eq!(b.bits, 0b1010_0001);
        b.set_unchecked(6, One);
        assert_eq!(b.bits, 0b1110_0001);

        b.set_unchecked(0, Zero);
        assert_eq!(b.bits, 0b1110_0000);
        b.set_unchecked(4, One);
        assert_eq!(b.bits, 0b1111_0000);
        b.set_unchecked(7, Zero);
        assert_eq!(b.bits, 0b0111_0000);
        b.set_unchecked(1, One);
        assert_eq!(b.bits, 0b0111_0010);
        b.set_unchecked(0, Zero);
        assert_eq!(b.bits, 0b0111_0010);
        b.set_unchecked(2, One);
        assert_eq!(b.bits, 0b0111_0110);
        b.set_unchecked(5, Zero);
        assert_eq!(b.bits, 0b0101_0110);
        b.set_unchecked(3, One);
        assert_eq!(b.bits, 0b0101_1110);
        b.set_unchecked(6, Zero);
        assert_eq!(b.bits, 0b0001_1110);
    }
}
