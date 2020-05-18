//! Utilities functions which do not linked to domain

use std::ops::{Div, Neg, Rem};

#[doc(hidden)]
#[macro_export]
/// Implements `From` trait for newtype-like enum variants
macro_rules! enum_trivial_from_impl {
    ($from:ty => $to:ty:$constructor:ident) => {
        impl From<$from> for $to {
            fn from(val: $from) -> Self {
                Self::$constructor(val)
            }
        }
    };
}

/// Allow conversion of a signed value into its unsigned equivalent
/// by dropping the sign away
pub(crate) trait ToUnsigned<U>: Default + Copy + PartialOrd + Neg<Output = Self> {
    /// represent the source (signed) type as target (unsigned) type
    fn as_type(self) -> U;

    /// Converts to unsigned absolute value
    fn unsigned_abs(self) -> (U, bool) {
        if self >= Self::default() {
            (self.as_type(), true)
        } else {
            ((-self).as_type(), false)
        }
    }
}

macro_rules! impl_unsigned_abs {
    ($from: tt -> $to: ty) => {
        impl ToUnsigned<$to> for $from {
            fn as_type(self) -> $to {
                self as $to
            }
        }
    };

    ($same: ty) => {
        impl ToUnsigned<$same> for $same {
            fn as_type(self) -> Self {
                self
            }
        }
    };
}

impl_unsigned_abs!(i8 -> u8);
impl_unsigned_abs!(i16 -> u16);
impl_unsigned_abs!(i32 -> u32);
impl_unsigned_abs!(i64 -> u64);
impl_unsigned_abs!(f64);

/// Strip the given character from the beginning or the end
pub(crate) trait StripChar {
    /// Strip the character from the beginning
    fn strip_prefix_char(self, ch: char) -> Option<String>;
    /// Strip the character from the end
    fn strip_suffix_char(self, ch: char) -> Option<String>;
    /// Split into the first character and the rest of the string
    fn split_first(self) -> Option<(char, String)>;
    /// Split into the last character and the rest of the string
    fn split_last(self) -> Option<(String, char)>;
}

impl StripChar for &str {
    fn strip_prefix_char(self, ch: char) -> Option<String> {
        if self.starts_with(ch) {
            let mut stripped = self.to_string();
            assert_eq!(stripped.remove(0), ch);
            Some(stripped)
        } else {
            None
        }
    }

    fn strip_suffix_char(self, ch: char) -> Option<String> {
        if self.ends_with(ch) {
            let mut stripped = self.to_string();
            assert_eq!(stripped.pop(), Some(ch));
            Some(stripped)
        } else {
            None
        }
    }

    fn split_first(self) -> Option<(char, String)> {
        self.chars().next().and_then(|head| {
            self.strip_prefix_char(head)
                .map(|stripped| (head, stripped))
        })
    }

    fn split_last(self) -> Option<(String, char)> {
        self.chars().last().and_then(|tail| {
            self.strip_suffix_char(tail)
                .map(|stripped| (stripped, tail))
        })
    }
}

/// Division and remainder in one step
pub fn div_mod<T>(divider: T, divisor: T) -> (T, T)
where
    T: Copy + Div<Output = T> + Rem<Output = T>,
{
    (divider / divisor, divider % divisor)
}

/// Round up the integer division when the remainder is big enough
pub(crate) trait RoundDiv {
    fn div_round(self, y: Self) -> Self;
}

macro_rules! impl_round_div {
    ($t: ty) => {
        impl RoundDiv for $t {
            fn div_round(self, y: Self) -> Self {
                let (quot, rem) = div_mod(self, y);
                if rem > (y >> 1) {
                    // > 0.5 rounds up
                    quot + 1
                } else {
                    // <= 0.5 rounds down
                    quot
                }
            }
        }
    };
}

impl_round_div!(u32);
impl_round_div!(u64);

const POW_10: [u32; 10] = [
    1_u32,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
];

/// The powers of 10
pub const fn pow_10(pow: usize) -> u32 {
    POW_10[pow]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsigned() {
        assert_eq!(7_i8.unsigned_abs(), (7_u8, true));
        assert_eq!((-7_i8).unsigned_abs(), (7_u8, false));

        assert_eq!(1283_i16.unsigned_abs(), (1283_u16, true));
        assert_eq!((-25_038_i16).unsigned_abs(), (25_038_u16, false));
    }

    //noinspection SpellCheckingInspection
    #[test]
    fn strip_prefix_matches() {
        let s = "Hello";
        assert_eq!(s.strip_prefix_char('H').unwrap(), "ello");
    }

    #[test]
    fn strip_prefix_no_match() {
        let s = "Hello";
        assert!(s.strip_prefix_char('W').is_none());
    }

    //noinspection SpellCheckingInspection
    #[test]
    fn strip_suffix_matches() {
        let s = "World";
        assert_eq!(s.strip_suffix_char('d').unwrap(), "Worl");
    }

    #[test]
    fn strip_suffix_no_match() {
        let s = "World";
        assert!(s.strip_suffix_char('o').is_none());
    }

    #[test]
    fn split_head() {
        let s = "Foo";
        assert_eq!(s.split_first().unwrap(), ('F', "oo".into()));
    }

    #[test]
    fn split_head_empty() {
        let s = "";
        assert!(s.split_first().is_none());
    }

    #[test]
    fn split_head_single() {
        let s = "Y";
        assert_eq!(s.split_first().unwrap(), ('Y', String::new()));
    }

    #[test]
    fn split_tail() {
        let s = "Buzz";
        assert_eq!(s.split_last().unwrap(), ("Buz".into(), 'z'));
    }

    #[test]
    fn split_tail_empty() {
        let s = "";
        assert!(s.split_last().is_none());
    }

    #[test]
    fn split_tail_single() {
        let s = "Y";
        assert_eq!(s.split_last().unwrap(), (String::new(), 'Y'));
    }

    #[test]
    fn test_div_mod() {
        assert_eq!(div_mod(15, 4), (3, 3));
        assert_eq!(div_mod(-100, 7), (-14, -2));
    }
}
