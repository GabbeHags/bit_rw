#![deny(unsafe_code)]

use std::fmt::{Binary, Debug, Display, Formatter};

#[derive(Debug)]
pub enum Error {
    IndexOutOfRange,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IndexOutOfRange => {
                f.write_str("The given index is larger than the number of bits.")
            }
            #[allow(unreachable_patterns)]
            _ => unimplemented!(),
        }
    }
}

macro_rules! cast_to_bit {
    ($bit:ident) => {{
        match $bit {
            0 => Bit::Zero,
            1 => Bit::One,
            _ => panic!("Could not cast {} because it is not a 1 or 0.", $bit),
        }
    }};
}
macro_rules! cast_from_bit {
    ($bit:ident) => {{
        match $bit {
            Bit::Zero => 0,
            Bit::One => 1,
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

macro_rules! impl_from_and_into_for_bit {
    ($($t:ty)*) => ($(
        impl From<$t> for Bit {
            fn from(bit: $t) -> Self {
                cast_to_bit!(bit)
            }
        }
        impl From<&$t> for Bit {
            fn from(bit: &$t) -> Self {
                cast_to_bit!(bit)
            }
        }
        impl From<Bit> for $t {
            fn from(bit: Bit) -> Self {
                cast_from_bit!(bit)
            }
        }
        impl From<&Bit> for $t {
            fn from(bit: &Bit) -> Self {
                cast_from_bit!(bit)
            }
        }
    )*)
}

impl_from_and_into_for_bit! { u8 u16 u32 u64 u128 usize}

macro_rules! impl_bits_for_size {
    ($(($name:ident, $size:ty, $index_type:ty))*) => ($(

    #[derive(Default)]
    #[doc = concat!(
        "Wrapper type of the primitive type `",
        stringify!($size),
        "` to be able to read/write to the bits."
    )]
    pub struct $name {
        bits: $size,
    }

    impl $name {

        #[doc = concat!("Creates a `", stringify!($name), "`")]
        /// , the input `bits` is the bits that is going to be interacted with.
        pub fn new(bits: $size) -> Self {
            Self { bits }
        }

        /// Shifts all bits to the left and inserts the `bit` at the left most bit.
        ///
        /// Shifting with bit [`Bit::Zero`] is the same as a normal shift left.
        ///
        /// # Example
        /// ```
        #[doc = concat!("use bit_rw::{", stringify!($name), ", Bit};")]
        ///
        #[doc = concat!("let mut b = ", stringify!($name), "::new(0);   // 0b0")]
        /// b.shift_left_with(Bit::One);  // 0b01
        /// b.shift_left_with(Bit::One);  // 0b011
        /// b.shift_left_with(Bit::Zero); // 0b0110
        ///
        /// assert_eq!(b, 6.into());
        /// ```
        pub fn shift_left_with(&mut self, bit: Bit) {
            self.bits <<= 1;
            if bit == Bit::One {
                self.bits |= 1;
            }
        }

        /// Shifts all bits to the right and inserts the `bit` at the right most bit.
        ///
        /// Shifting with bit [`Bit::Zero`] is the same as a normal shift right.
        ///
        /// # Example
        /// ```
        #[doc = concat!("use bit_rw::{", stringify!($name), ", Bit};")]
        ///
        #[doc = concat!("let mut b = ", stringify!($name), "::new(0);  // 0b0")]
        /// b.shift_right_with(Bit::One);     // 0b1000...
        /// // b.shift_right_with(Bit::One);  // 0b11000...
        /// // b.shift_right_with(Bit::Zero); // 0b011000...
        ///
        /// // assert_eq!(b, (0b011000...).into());
        #[doc = concat!(
            "assert_eq!(b, 2_",
            stringify!($size),
            ".pow(<",
            stringify!($size),
            ">::BITS-1).into());"
        )]
        /// ```
        pub fn shift_right_with(&mut self, bit: Bit) {
            self.bits >>= 1;
            if bit == Bit::One {
                self.bits |= 1 << (<$size>::BITS-1);
            }
        }

        pub fn get_and_set<F: FnOnce(Bit) -> Bit>(&mut self, index: $index_type, f: F) -> Result<(), Error> {
            let bit = self.get(index)?;
            self.set_unchecked(index, f(bit));
            Ok(())
        }

        pub fn get_and_set_unchecked<F: FnOnce(Bit) -> Bit>(&mut self, index: $index_type, f: F) {
            self.set_unchecked(index, f(self.get_unchecked(index)));
        }

        pub fn set(&mut self, index: $index_type, bit: Bit) -> Result<(), Error> {
            if (0..(<$size>::BITS as $index_type)).contains(&index) {
                self.set_unchecked(index, bit);
                Ok(())
            } else {
                Err(Error::IndexOutOfRange)
            }
        }

        pub fn set_unchecked(&mut self, index: $index_type, bit: Bit) {
            match bit {
                Bit::Zero => self.bits &= !(1 << index),
                Bit::One => self.bits |= 1 << index,
            }
        }

        pub fn get(&self, index: $index_type) -> Result<Bit, Error> {
             if (0..(<$size>::BITS as $index_type)).contains(&index) {
                Ok(self.get_unchecked(index))
            } else {
                Err(Error::IndexOutOfRange)
            }
        }

        pub fn get_unchecked(&self, index: $index_type) -> Bit {
            if self.bits & 1 << index == 0 {
                Bit::Zero
            } else {
                Bit::One
            }
        }
    }

    impl From<$size> for $name {
        fn from(bits: $size) -> Self {
            Self::new(bits)
        }
    }

    impl From<$name> for $size {
        fn from(bits: $name) -> Self {
            bits.bits
        }
    }

    impl PartialEq<Self> for $name {
        fn eq(&self, other: &Self) -> bool {
            self.bits == other.bits
        }
    }

    impl Eq for $name {}
    )*)
}

impl_bits_for_size! { (Bits8, u8, u8) (Bits16, u16, u16) (Bits32, u32, u32) (Bits64, u64, u32) (Bits128, u128, u32) }

macro_rules! impl_debug_for_bits {
    ($(($name:ident, $bits_len:literal))*) => ($(
    impl Binary for $name {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            f.write_fmt(format_args!(concat!("{:0", $bits_len, "b}"), &self.bits))
        }
    }

    impl Debug for $name {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            f.write_str(concat!(stringify!($name), " { bits: "))?;
            std::fmt::Binary::fmt(&self, f)?;
            f.write_str(" }")
        }
    }
    )*)
}

impl_debug_for_bits! { (Bits8, 8) (Bits16, 16) (Bits32, 32) (Bits64, 64) (Bits128, 128) }

#[cfg(test)]
mod tests_bits64 {
    use crate::Bit::*;
    use crate::*;

    #[test]
    fn get_and_set_set_if_one() {
        let mut b = Bits64::new(!0);
        let mut eq: u64 = !0;
        for i in 0..64 {
            b.get_and_set(i, |bit| if bit == One { Zero } else { bit })
                .unwrap();
            eq <<= 1;
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_and_set_set_invert() {
        let mut b1 = Bits64::new(0);
        let mut b2 = Bits64::new(!0);
        let mut eq1: u64 = 0;
        let mut eq2: u64 = !0;
        for i in 0..64 {
            b1.get_and_set(i, |bit| bit.invert()).unwrap();
            b2.get_and_set(i, |bit| bit.invert()).unwrap();
            eq1 |= 1 << i;
            eq2 <<= 1;
            assert_eq!(b1, eq1.into());
            assert_eq!(b2, eq2.into());
        }
    }
}
#[cfg(test)]
mod tests_bits8 {
    use crate::Bit::*;
    use crate::*;

    #[test]
    fn get_and_set_out_of_range() {
        assert!(matches!(
            Bits8::default().get_and_set(8, |_| One).unwrap_err(),
            Error::IndexOutOfRange
        ));
    }

    #[test]
    fn get_and_set_set_if_one() {
        let mut b = Bits8::new(!0);
        let mut eq: u8 = !0;
        for i in 0..8 {
            b.get_and_set(i, |bit| if bit == One { Zero } else { bit })
                .unwrap();
            eq <<= 1;
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_and_set_set_if_zero() {
        let mut b = Bits8::new(0);
        let mut eq: u8 = 0;
        for i in 0..8 {
            b.get_and_set(i, |bit| if bit == Zero { One } else { bit })
                .unwrap();
            eq |= 1 << i;
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_and_set_set_invert() {
        let mut b1 = Bits8::new(0);
        let mut b2 = Bits8::new(!0);
        let mut eq1: u8 = 0;
        let mut eq2: u8 = !0;
        for i in 0..8 {
            b1.get_and_set(i, |bit| bit.invert()).unwrap();
            b2.get_and_set(i, |bit| bit.invert()).unwrap();
            eq1 |= 1 << i;
            eq2 <<= 1;
            assert_eq!(b1, eq1.into());
            assert_eq!(b2, eq2.into());
        }
    }

    #[test]
    #[should_panic]
    fn get_and_set_unchecked_panic() {
        Bits8::default().get_and_set_unchecked(8, |_| One)
    }

    #[test]
    fn get_and_set_unchecked_set_if_one() {
        let mut b = Bits8::new(0b1111_1111);
        let mut eq: u8 = !0;
        for i in 0..8 {
            b.get_and_set_unchecked(i, |bit| if bit == One { Zero } else { bit });
            eq <<= 1;
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_and_set_unchecked_set_if_zero() {
        let mut b = Bits8::new(0);
        let mut eq: u8 = 0;
        for i in 0..8 {
            b.get_and_set_unchecked(i, |bit| if bit == Zero { One } else { bit });
            eq |= 1 << i;
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_and_set_unchecked_set_invert() {
        let mut b1 = Bits8::new(0);
        let mut b2 = Bits8::new(!0);
        let mut eq1: u8 = 0;
        let mut eq2: u8 = !0;
        for i in 0..8 {
            b1.get_and_set_unchecked(i, |bit| bit.invert());
            b2.get_and_set_unchecked(i, |bit| bit.invert());
            eq1 |= 1 << i;
            eq2 <<= 1;
            assert_eq!(b1, eq1.into());
            assert_eq!(b2, eq2.into());
        }
    }

    #[test]
    fn shift_left_with_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b1.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b11.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b111.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b1111.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b11111.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b111111.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b1111111.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b11111111.into());
    }
    #[test]
    fn shift_left_with_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0.into());
    }
    #[test]
    fn shift_left_with_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b1.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0b10.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b101.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0b1010.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b1_0101.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0b1010_10.into());
        b.shift_left_with(One);
        assert_eq!(b, 0b101_0101.into());
        b.shift_left_with(Zero);
        assert_eq!(b, 0b1010_1010.into());
    }

    #[test]
    fn shift_right_with_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1000_0000.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1100_0000.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1110_0000.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1111_0000.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1111_1000.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1111_1100.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1111_1110.into());
        b.shift_right_with(One);
        assert_eq!(b, 0b1111_1111.into());
    }

    #[test]
    fn shift_right_with_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b, 0.into());
        for _ in 0..8 {
            b.shift_right_with(Zero);
            assert_eq!(b, 0.into());
        }
    }

    #[test]
    fn shift_right_with_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        let mut eq: u8 = 0;
        for i in 0..8 {
            eq >>= 1;
            if i % 2 == 0 {
                b.shift_right_with(One);
                eq |= 1 << 7;
            } else {
                b.shift_right_with(Zero);
            }
            assert_eq!(b, eq.into());
        }
    }

    #[test]
    fn get_out_of_range() {
        assert!(matches!(
            Bits8::default().get(8).unwrap_err(),
            Error::IndexOutOfRange
        ));
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
        assert_eq!(b, 0b0.into());
        b.set(0, One).unwrap();
        assert_eq!(b, 0b0000_0001.into());
        b.set(4, One).unwrap();
        assert_eq!(b, 0b0001_0001.into());
        b.set(7, One).unwrap();
        assert_eq!(b, 0b1001_0001.into());
        b.set(1, One).unwrap();
        assert_eq!(b, 0b1001_0011.into());
        b.set(0, One).unwrap();
        assert_eq!(b, 0b1001_0011.into());
        b.set(2, One).unwrap();
        assert_eq!(b, 0b1001_0111.into());
        b.set(5, One).unwrap();
        assert_eq!(b, 0b1011_0111.into());
        b.set(3, One).unwrap();
        assert_eq!(b, 0b1011_1111.into());
        b.set(6, One).unwrap();
        assert_eq!(b, 0b1111_1111.into());
    }

    #[test]
    fn set_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.set(0, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(4, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(7, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(1, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(0, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(2, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(5, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(3, Zero).unwrap();
        assert_eq!(b, 0b0.into());
        b.set(6, Zero).unwrap();
        assert_eq!(b, 0b0.into());
    }

    #[test]
    fn set_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.set(0, One).unwrap();
        assert_eq!(b, 0b0000_0001.into());
        b.set(4, Zero).unwrap();
        assert_eq!(b, 0b0000_0001.into());
        b.set(7, One).unwrap();
        assert_eq!(b, 0b1000_0001.into());
        b.set(1, Zero).unwrap();
        assert_eq!(b, 0b1000_0001.into());
        b.set(0, One).unwrap();
        assert_eq!(b, 0b1000_0001.into());
        b.set(2, Zero).unwrap();
        assert_eq!(b, 0b1000_0001.into());
        b.set(5, One).unwrap();
        assert_eq!(b, 0b1010_0001.into());
        b.set(3, Zero).unwrap();
        assert_eq!(b, 0b1010_0001.into());
        b.set(6, One).unwrap();
        assert_eq!(b, 0b1110_0001.into());

        b.set(0, Zero).unwrap();
        assert_eq!(b, 0b1110_0000.into());
        b.set(4, One).unwrap();
        assert_eq!(b, 0b1111_0000.into());
        b.set(7, Zero).unwrap();
        assert_eq!(b, 0b0111_0000.into());
        b.set(1, One).unwrap();
        assert_eq!(b, 0b0111_0010.into());
        b.set(0, Zero).unwrap();
        assert_eq!(b, 0b0111_0010.into());
        b.set(2, One).unwrap();
        assert_eq!(b, 0b0111_0110.into());
        b.set(5, Zero).unwrap();
        assert_eq!(b, 0b0101_0110.into());
        b.set(3, One).unwrap();
        assert_eq!(b, 0b0101_1110.into());
        b.set(6, Zero).unwrap();
        assert_eq!(b, 0b0001_1110.into());
    }

    #[test]
    #[should_panic]
    fn set_unchecked_panic() {
        Bits8::default().set_unchecked(8, One);
    }

    #[test]
    fn set_unchecked_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.set_unchecked(0, One);
        assert_eq!(b, 0b0000_0001.into());
        b.set_unchecked(4, One);
        assert_eq!(b, 0b0001_0001.into());
        b.set_unchecked(7, One);
        assert_eq!(b, 0b1001_0001.into());
        b.set_unchecked(1, One);
        assert_eq!(b, 0b1001_0011.into());
        b.set_unchecked(0, One);
        assert_eq!(b, 0b1001_0011.into());
        b.set_unchecked(2, One);
        assert_eq!(b, 0b1001_0111.into());
        b.set_unchecked(5, One);
        assert_eq!(b, 0b1011_0111.into());
        b.set_unchecked(3, One);
        assert_eq!(b, 0b1011_1111.into());
        b.set_unchecked(6, One);
        assert_eq!(b, 0b1111_1111.into());
    }

    #[test]
    fn set_unchecked_zeros() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.set_unchecked(0, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(4, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(7, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(1, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(0, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(2, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(5, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(3, Zero);
        assert_eq!(b, 0b0.into());
        b.set_unchecked(6, Zero);
        assert_eq!(b, 0b0.into());
    }

    #[test]
    fn set_unchecked_zeros_and_ones() {
        let mut b = Bits8::default();
        assert_eq!(b, 0b0.into());
        b.set_unchecked(0, One);
        assert_eq!(b, 0b0000_0001.into());
        b.set_unchecked(4, Zero);
        assert_eq!(b, 0b0000_0001.into());
        b.set_unchecked(7, One);
        assert_eq!(b, 0b1000_0001.into());
        b.set_unchecked(1, Zero);
        assert_eq!(b, 0b1000_0001.into());
        b.set_unchecked(0, One);
        assert_eq!(b, 0b1000_0001.into());
        b.set_unchecked(2, Zero);
        assert_eq!(b, 0b1000_0001.into());
        b.set_unchecked(5, One);
        assert_eq!(b, 0b1010_0001.into());
        b.set_unchecked(3, Zero);
        assert_eq!(b, 0b1010_0001.into());
        b.set_unchecked(6, One);
        assert_eq!(b, 0b1110_0001.into());

        b.set_unchecked(0, Zero);
        assert_eq!(b, 0b1110_0000.into());
        b.set_unchecked(4, One);
        assert_eq!(b, 0b1111_0000.into());
        b.set_unchecked(7, Zero);
        assert_eq!(b, 0b0111_0000.into());
        b.set_unchecked(1, One);
        assert_eq!(b, 0b0111_0010.into());
        b.set_unchecked(0, Zero);
        assert_eq!(b, 0b0111_0010.into());
        b.set_unchecked(2, One);
        assert_eq!(b, 0b0111_0110.into());
        b.set_unchecked(5, Zero);
        assert_eq!(b, 0b0101_0110.into());
        b.set_unchecked(3, One);
        assert_eq!(b, 0b0101_1110.into());
        b.set_unchecked(6, Zero);
        assert_eq!(b, 0b0001_1110.into());
    }
}
