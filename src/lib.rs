#![deny(unsafe_code)]

use paste::paste;
use std::fmt::{Binary, Debug, Display, Formatter};

#[derive(Debug)]
/// Errors in the bit_rw crate.
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
/// Represents one bit.
pub enum Bit {
    Zero,
    One,
}

impl Bit {
    /// Inverts the bit.
    ///
    /// # Example
    /// ```
    /// use bit_rw::Bit;
    ///
    /// assert_eq!(Bit::One, Bit::Zero.invert())
    /// ```
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

impl_from_and_into_for_bit! { u8 i8 u16 i16 u32 i32 u64 i64 u128 i128 usize isize}

macro_rules! impl_bits {
    ($name:ident, $size:ty, $index_type:ty, $bit_len:literal) => {
        paste!{
            #[derive(Default)]
            #[doc = "Wrapper type of the primitive type `" $size "` to be able to read/write to the bits. The memory size of this struct is the same as the primitive type."]
            pub struct $name {
                bits: $size,
            }
        }

        impl $name {
            paste!{
                #[doc = "Creates a [`" $name "`], the input `bits` is the bits that is going to be interacted with."]
                pub fn new(bits: $size) -> Self {
                    Self { bits }
                }
            }

            paste!{
                /// Shifts all bits to the left and inserts the `bit` at the left most bit.
                ///
                /// Shifting with bit [`Bit::Zero`] is the same as a normal shift left.
                ///
                /// # Example
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0);   // 0b0"]
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
            }

            paste!{
                /// Shifts all bits to the right and inserts the `bit` at the right most bit.
                ///
                /// Shifting with bit [`Bit::Zero`] is the same as a normal shift right.
                ///
                /// # Example
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0);  // 0b0"]
                /// b.shift_right_with(Bit::One);     // 0b1000...
                /// // b.shift_right_with(Bit::One);  // 0b11000...
                /// // b.shift_right_with(Bit::Zero); // 0b011000...
                ///
                /// // assert_eq!(b, (0b011000...).into());
                #[doc = "assert_eq!(b, 2_" $size ".pow(" $bit_len "-1).into());"]
                /// ```
                pub fn shift_right_with(&mut self, bit: Bit) {
                    self.bits >>= 1;
                    if bit == Bit::One {
                        self.bits |= 1 << ($bit_len-1);
                    }
                }
            }

            paste! {
                /// Gets the bit at `index` and pass it to `func`, then set the bit at `index` to the result of `func`.
                ///
                /// # Errors
                /// Will return [`Error::IndexOutOfRange`] if `index` is more than the number of bits.
                ///
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0); // 0b0000"]
                ///
                /// // Here we invert the bit at index 3
                /// b.get_and_set(3, |bit| bit.invert()).unwrap(); //0b1000
                ///
                /// assert_eq!(b, 0b1000.into())
                /// ```
                pub fn get_and_set<Func: FnOnce(Bit) -> Bit>(
                    &mut self,
                    index: $index_type,
                    func: Func,
                ) -> Result<(), Error> {
                    let bit = self.get(index)?;
                    self.set_unchecked(index, func(bit));
                    Ok(())
                }
            }

            paste!{
                /// Gets the bit at `index` and pass it to `func`, then set the bit at `index` to the result of `func`.
                ///
                /// This method is the same as [`get_and_set`] but won't do a range check on `index`.
                /// If the `index` is more than the number of bits, the result can be unexpected.
                ///
                #[doc = "[`get_and_set`]:" $name "::get_and_set"]
                ///
                /// # Panics
                /// Will panic in debug build if `index` is more than the number of bits because of left shift overflow.
                ///
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0); // 0b0000"]
                ///
                /// // Here we invert the bit at index 3. In this case it will go from 0 to 1
                /// b.get_and_set_unchecked(3, |bit| bit.invert()); //0b1000
                ///
                /// assert_eq!(b, 0b1000.into())
                /// ```
                pub fn get_and_set_unchecked<Func: FnOnce(Bit) -> Bit>(
                    &mut self,
                    index: $index_type,
                    func: Func,
                ) {
                    self.set_unchecked(index, func(self.get_unchecked(index)));
                }
            }

            paste! {
                /// Sets the bit at `index` to `bit`.
                ///
                /// # Errors
                /// Will return [`Error::IndexOutOfRange`] if `index` is more than the number of bits.
                ///
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0); // 0b0000"]
                ///
                /// // Here we set the bit at index 3 to 1
                /// b.set(3, Bit::One).unwrap(); //0b1000
                ///
                /// assert_eq!(b, 0b1000.into())
                /// ```
                pub fn set(&mut self, index: $index_type, bit: Bit) -> Result<(), Error> {
                    if (0..$bit_len).contains(&index) {
                        self.set_unchecked(index, bit);
                        Ok(())
                    } else {
                        Err(Error::IndexOutOfRange)
                    }
                }
            }
            paste!{
                /// Sets the bit at `index` to `bit`.
                ///
                /// If the `index` is more than the number of bits, the result can be unexpected.
                /// 
                /// # Panics
                /// Will panic in debug build if `index` is more than the number of bits because of left shift overflow.
                ///
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0); // 0b0000"]
                ///
                /// // Here we set the bit at index 3 to 1
                /// b.set(3, Bit::One); //0b1000
                ///
                /// assert_eq!(b, 0b1000.into())
                /// ```
                pub fn set_unchecked(&mut self, index: $index_type, bit: Bit) {
                    match bit {
                        Bit::Zero => self.bits &= !(1 << index),
                        Bit::One => self.bits |= 1 << index,
                    }
                }
            }

            paste!{
                /// Returns the bit at `index`.
                ///
                /// # Errors
                /// Will return [`Error::IndexOutOfRange`] if `index` is more than the number of bits.
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                ///
                #[doc = "let mut b = " $name "::new(0b0100);"]
                ///
                /// // Here we get the bit at index 2
                /// let bit = b.get(2).unwrap();  //0b0100
                ///
                /// assert_eq!(bit, Bit::One);
                /// ```
                pub fn get(&self, index: $index_type) -> Result<Bit, Error> {
                    if (0..$bit_len).contains(&index) {
                        Ok(self.get_unchecked(index))
                    } else {
                        Err(Error::IndexOutOfRange)
                    }
                }
            }

            paste!{
                /// Returns the bit at `index`.
                /// 
                /// If the `index` is more than the number of bits, the result can be unexpected.
                /// 
                /// # Panics
                /// Will panic in debug build if `index` is more than the number of bits because of left shift overflow.
                ///
                /// # Examples
                /// ```
                #[doc = "use bit_rw::{" $name ", Bit};"]
                #[doc = "let mut b = " $name "::new(0b0100);"]
                ///
                /// // Here we get the bit at index 2
                /// let bit = b.get_unchecked(2);  //0b0100
                ///
                /// assert_eq!(bit, Bit::One);
                /// ```
                pub fn get_unchecked(&self, index: $index_type) -> Bit {
                    if self.bits & 1 << index == 0 {
                        Bit::Zero
                    } else {
                        Bit::One
                    }
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
    };
}

macro_rules! impl_debug_for_bits {
    ($name:ident, $bits_len:literal) => {
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
    };
}

macro_rules! impl_iterator_for_bits {
    ($name:ident, $iterator_name:ident, $iterator_consuming_name:ident, $index_type:ty) => {
        pub struct $iterator_name<'a> {
            bits: &'a $name,
            index: $index_type,
        }

        pub struct $iterator_consuming_name {
            bits: $name,
            index: $index_type,
        }

        impl<'a> Iterator for $iterator_name<'a> {
            type Item = Bit;
            fn next(&mut self) -> Option<Self::Item> {
                self.index += 1;
                self.bits.get(self.index - 1).ok()
            }
        }

        impl<'a> Iterator for $iterator_consuming_name {
            type Item = Bit;
            fn next(&mut self) -> Option<Self::Item> {
                self.index += 1;
                self.bits.get(self.index - 1).ok()
            }
        }

        impl<'a> IntoIterator for &'a $name {
            type Item = Bit;
            type IntoIter = $iterator_name<'a>;

            fn into_iter(self) -> Self::IntoIter {
                $iterator_name {
                    bits: self,
                    index: 0,
                }
            }
        }

        impl IntoIterator for $name {
            type Item = Bit;
            type IntoIter = $iterator_consuming_name;

            fn into_iter(self) -> Self::IntoIter {
                $iterator_consuming_name {
                    bits: self,
                    index: 0,
                }
            }
        }
    };
}

macro_rules! impl_all_bits {
    // (Struct name, number of bits, type for indexing)
    ($(($name:ident, $bits_len:literal, $index_type:ty))*) => ($(
        paste!{
            impl_bits!($name, [<u $bits_len>], $index_type, $bits_len);
            impl_debug_for_bits!($name, $bits_len);
            impl_iterator_for_bits!($name, [<$name Iterator>], [<$name IteratorConsuming>], $index_type);
        }
    )*);
}

impl_all_bits! {
    // (Struct name, number of bits, type for indexing)
    (Bits8, 8, u8)
    (Bits16, 16, u16)
    (Bits32, 32, u32)
    (Bits64, 64, u32)
    (Bits128, 128, u32)
}

#[cfg(test)]
mod bits_tests {
    use paste::paste;

    macro_rules! create_bits_tests {
    ($(($name:ident, $inner_type:ty, $index_type:ty))*) => ($(
    paste! {
        mod [<tests_ $name:lower>] {
            use crate::Bit::*;
            use crate::*;
            #[test]
            fn get_and_set_set_if_one() {
                let mut b = $name::new(!0);
                let mut eq: $inner_type = !0;
                for i in 0..($inner_type::BITS as $index_type) {
                    b.get_and_set(i, |bit| if bit == One { Zero } else { bit })
                        .unwrap();
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }

            #[test]
            fn get_and_set_set_if_zero() {
                let mut b = $name::new(0);
                let mut eq: $inner_type = 0;
                for i in 0..($inner_type::BITS as $index_type) {
                    b.get_and_set(i, |bit| if bit == Zero { One } else { bit })
                        .unwrap();
                    eq |= 1 << i;
                    assert_eq!(b, eq.into());
                }
            }

            #[test]
            fn get_and_set_set_invert() {
                let mut b1 = $name::new(0);
                let mut b2 = $name::new(!0);
                let mut eq1: $inner_type = 0;
                let mut eq2: $inner_type = !0;
                for i in 0..($inner_type::BITS as $index_type) {
                    b1.get_and_set(i, |bit| bit.invert()).unwrap();
                    b2.get_and_set(i, |bit| bit.invert()).unwrap();
                    eq1 |= 1 << i;
                    eq2 <<= 1;
                    assert_eq!(b1, eq1.into());
                    assert_eq!(b2, eq2.into());
                }
            }

            #[test]
            fn iterator_test() {
                let b = $name::new(0);
                let mut count = 0;
                for bit in &b {
                    count += 1;
                    assert_eq!(bit, Zero);
                }
                assert_eq!(b, 0.into());
                assert_eq!(count, $inner_type::BITS);
                
                let b = $name::new(!0);
                count = 0;
        
                for bit in b {
                    count += 1;
                    assert_eq!(bit, One);
                }
                assert_eq!(count, $inner_type::BITS);
            }

            #[test]
            fn get_and_set_out_of_range() {
                assert!(matches!(
                    $name::default()
                    .get_and_set($inner_type::BITS as $index_type, |_| One)
                    .unwrap_err(),
                    Error::IndexOutOfRange
                ));
            }

            #[cfg(debug_assertions)]
            #[test]
            #[should_panic]
            fn get_and_set_unchecked_panic() {
                $name::default().get_and_set_unchecked($inner_type::BITS as $index_type, |_| One);
            }

            #[test]
            fn get_and_set_unchecked_set_if_one() {
                let mut b = $name::new(!0);
                let mut eq: $inner_type = !0;
                for i in 0..($inner_type::BITS as $index_type) {
                    b.get_and_set_unchecked(i, |bit| if bit == One { Zero } else { bit });
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }
        
            #[test]
            fn get_and_set_unchecked_set_if_zero() {
                let mut b = $name::new(0);
                let mut eq: $inner_type = 0;
                for i in 0..($inner_type::BITS as $index_type) {
                    b.get_and_set_unchecked(i, |bit| if bit == Zero { One } else { bit });
                    eq |= 1 << i;
                    assert_eq!(b, eq.into());
                }
            }
        
            #[test]
            fn get_and_set_unchecked_set_invert() {
                let mut b1 = $name::new(0);
                let mut b2 = $name::new(!0);
                let mut eq1: $inner_type = 0;
                let mut eq2: $inner_type = !0;
                for i in 0..($inner_type::BITS as $index_type) {
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
                let mut b = $name::default();
                let mut eq: $inner_type = 1;
                assert_eq!(b, 0b0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    b.shift_left_with(One);
                    eq |= 1 << i;
                    assert_eq!(b, eq.into());
                }
            }

            #[test]
            fn shift_left_with_zeros() {
                let mut b = $name::default();
                assert_eq!(b, 0b0.into());
                for _ in 0..($inner_type::BITS as $index_type) {
                    b.shift_left_with(Zero);
                    assert_eq!(b, 0.into());
                }
            }
            #[test]
            fn shift_left_with_zeros_and_ones() {
                let mut b = $name::default();
                let mut eq = 0;
                assert_eq!(b, 0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    b.shift_left_with((i % 2).into());
                    eq <<= 1;
                    if (i % 2) == 1 {
                        eq |= 1;
                    }
                    assert_eq!(b, eq.into());
                }
            }

            #[test]
            fn shift_right_with_ones() {
                let mut b = $name::default();
                let mut eq = 0;
                assert_eq!(b, 0.into());
                for _ in 0..($inner_type::BITS as $index_type) {
                    b.shift_right_with(One);
                    eq ^= !0;
                    eq >>= 1;
                    eq ^= !0;
                    assert_eq!(b, eq.into());
                }
            }
            #[test]
            fn shift_right_with_zeros() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                for _ in 0..($inner_type::BITS as $index_type) {
                    b.shift_right_with(Zero);
                    assert_eq!(b, 0.into());
                }
            }
            #[test]
            fn shift_right_with_zeros_and_ones() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                let mut eq = 0;
                for i in 0..($inner_type::BITS as $index_type) {
                    eq >>= 1;
                    if i % 2 == 0 {
                        b.shift_right_with(One);
                        eq |= 1 << ($inner_type::BITS - 1);
                    } else {
                        b.shift_right_with(Zero);
                    }
                    assert_eq!(b, eq.into());
                }
            }
            #[test]
            fn get_out_of_range() {
                assert!(matches!(
                    $name::default().get($inner_type::BITS as $index_type).unwrap_err(),
                    Error::IndexOutOfRange
                ));
            }

            #[test]
            fn get_zeros_and_ones() {
                // setup
                let mut b = $name::default();
                for i in 0..($inner_type::BITS as $index_type) {
                    if i % 2 == 0 {
                        b.set_unchecked(i, One);
                    }
                }
                // test
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get(i).unwrap();
                    if i % 2 == 0 {
                        assert_eq!(bit, 1.into());
                    } else {
                        assert_eq!(bit, 0.into());
                    }
                }
            }

            #[test]
            fn get_ones() {
                let b = $name::new(!0);
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get(i).unwrap();
                    assert_eq!(bit, 1.into());
                }
            }
            #[test]
            fn get_zeros() {
                let b = $name::new(0);
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get(i).unwrap();
                    assert_eq!(bit, 0.into());
                }
            }
        
            #[cfg(debug_assertions)]
            #[test]
            #[should_panic]
            fn get_unchecked_panic() {
                $name::default().get_unchecked($inner_type::BITS as $index_type);
            }

            #[test]
            fn get_unchecked_zeros_and_ones() {
                // setup
                let mut b = $name::default();
                for i in 0..($inner_type::BITS as $index_type) {
                    if i % 2 == 0 {
                        b.set_unchecked(i, One);
                    }
                }
                // test
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get_unchecked(i);
                    if i % 2 == 0 {
                        assert_eq!(bit, 1.into());
                    } else {
                        assert_eq!(bit, 0.into());
                    }
                }
            }
        
            #[test]
            fn get_unchecked_ones() {
                let b = $name::new(!0);
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get_unchecked(i);
                    assert_eq!(bit, 1.into());
                }
            }
            #[test]
            fn get_unchecked_zeros() {
                let b = $name::new(0);
                for i in 0..($inner_type::BITS as $index_type) {
                    let bit = b.get_unchecked(i);
                    assert_eq!(bit, 0.into());
                }
            }
        
            #[test]
            fn set_out_of_range() {
                assert!(matches!(
                    $name::default().set($inner_type::BITS as $index_type, One).unwrap_err(),
                    Error::IndexOutOfRange
                ));
            }

            #[cfg(debug_assertions)]
            #[test]
            #[should_panic]
            fn set_unchecked_panic() {
                $name::default().set_unchecked($inner_type::BITS as $index_type, One);
            }

            #[test]
            fn set_zeros_to_ones() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), Zero);
                    b.set(i, One).unwrap();
                    assert_eq!(b.get_unchecked(i), One);
                }
                assert_eq!(b, (!0).into());
            }

            #[test]
            fn set_ones_to_zero() {
                let mut b = $name::new(!0);
                let mut eq = !0;
                assert_eq!(b, (!0).into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), One);
                    b.set(i, Zero).unwrap();
                    assert_eq!(b.get_unchecked(i), Zero);
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }
            #[test]
            fn set_zeros_and_ones() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), Zero);
                    b.set(i, One).unwrap();
                    assert_eq!(b.get_unchecked(i), One);
                }

                let mut eq = !0;
                assert_eq!(b, (!0).into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), One);
                    b.set(i, Zero).unwrap();
                    assert_eq!(b.get_unchecked(i), Zero);
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }

            #[test]
            fn set_unchecked_zeros_to_ones() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), Zero);
                    b.set_unchecked(i, One);
                    assert_eq!(b.get_unchecked(i), One);
                }
                assert_eq!(b, (!0).into());
            }

            #[test]
            fn set_unchecked_ones_to_zero() {
                let mut b = $name::new(!0);
                let mut eq = !0;
                assert_eq!(b, (!0).into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), One);
                    b.set_unchecked(i, Zero);
                    assert_eq!(b.get_unchecked(i), Zero);
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }
            #[test]
            fn set_unchecked_zeros_and_ones() {
                let mut b = $name::default();
                assert_eq!(b, 0.into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), Zero);
                    b.set_unchecked(i, One);
                    assert_eq!(b.get_unchecked(i), One);
                }

                let mut eq = !0;
                assert_eq!(b, (!0).into());
                for i in 0..($inner_type::BITS as $index_type) {
                    assert_eq!(b.get_unchecked(i), One);
                    b.set_unchecked(i, Zero);
                    assert_eq!(b.get_unchecked(i), Zero);
                    eq <<= 1;
                    assert_eq!(b, eq.into());
                }
            }
        }
    }
    )*);
    }

    create_bits_tests! {
        // (Struct name, inner type, type for indexing)
        (Bits8, u8, u8)
        (Bits16, u16, u16)
        (Bits32, u32, u32)
        (Bits64, u64, u32)
        (Bits128, u128, u32)
    }
}




