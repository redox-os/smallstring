#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

extern crate smallvec;

#[cfg(not(feature = "std"))]
extern crate alloc;
#[cfg(not(feature = "std"))]
use alloc::Vec;
#[cfg(not(feature = "std"))]
use alloc::String;

#[cfg(not(feature = "std"))]
mod std {
    pub use core::*;
}

use std::str::{self, Chars};
use std::ptr;
use std::ops::{Deref, DerefMut, RangeBounds};
use std::borrow::Borrow;
use std::iter::{FusedIterator, FromIterator, IntoIterator};
use std::fmt;

use smallvec::{Array, SmallVec};

#[cfg(feature = "std")]
use std::ffi::OsStr;

#[derive(Clone, Default, PartialOrd, Ord)]
pub struct SmallString<B: Array<Item = u8> = [u8; 8]> {
    buffer: SmallVec<B>,
}

impl<'a, B: Array<Item = u8>> SmallString<B> {
    /// Construct an empty string.
    pub fn new() -> Self {
        SmallString {
            buffer: SmallVec::new(),
        }
    }

    /// Constructs an empty string with enough capacity pre-allocated to store
    /// at least `n` bytes worth of characters.
    ///
    /// Will create a heap allocation if and only if `n` is larger than the
    /// inline capacity.
    pub fn with_capacity(n: usize) -> Self {
        SmallString {
            buffer: SmallVec::with_capacity(n),
        }
    }

    /// Constructs a new `SmallString` from a `String` without copying elements.
    pub fn from_string(string: String) -> Self {
        SmallString {
            buffer: SmallVec::from_vec(string.into()),
        }
    }

    pub fn from_str(s: &str) -> Self {
        SmallString {
            buffer: SmallVec::from_slice(s.as_bytes()),
        }
    }

    /// The maximum number of bytes this string can hold inline.
    pub fn inline_size(&self) -> usize {
        self.buffer.inline_size()
    }

    /// The length of this string in bytes.
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Returns `true` if the string is empty.
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// The maximum number of bytes this string can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.buffer.capacity()
    }

    /// Returns `true` if the string has spilled into a heap-allocated buffer.
    pub fn spilled(&self) -> bool {
        self.buffer.spilled()
    }

    /// Appends the given `char` to the end of this string.
    pub fn push(&mut self, ch: char) {
        match ch.len_utf8() {
            1 => self.buffer.push(ch as u8),
            _ => self.buffer
                .extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes()),
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns `None` if this string is empty.
    pub fn pop(&mut self) -> Option<char> {
        // copied from String::pop implementation.
        let ch = match self.chars().rev().next() {
            Some(ch) => ch,
            None => return None,
        };

        let new_len = self.len() - ch.len_utf8();

        // self.buffer.set_len might be more efficient, but this *should*
        // compile down to the same thing, and it is more safe in case
        // SmallVec::set_len's implementation changes.
        self.buffer.truncate(new_len);

        Some(ch)
    }

    /// Appends a given string slice onto the end of this string.
    pub fn push_str(&mut self, string: &str) {
        self.buffer.extend_from_slice(string.as_bytes())
    }

    /// Reserve capacity for `additional` bytes to be inserted.
    ///
    /// May reserve more space to avoid frequent reallocations.
    ///
    /// If the new capacity would overflow `usize` then it will be set to
    /// `usize::max_value()` instead. (This means that inserting additional new
    /// elements is not guaranteed to be possible after calling this function.)
    pub fn reserve(&mut self, additional: usize) {
        self.buffer.reserve(additional)
    }

    /// Reserve the minimum capacity for `additional` more bytes to be inserted.
    ///
    /// Panics if new capacity overflows `usize`.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.buffer.reserve_exact(additional)
    }

    /// Shrink the capacity of this `String` to match its length.
    ///
    /// When possible, this will move data from an external heap buffer to the
    /// string's inline storage.
    pub fn shrink_to_fit(&mut self) {
        self.buffer.shrink_to_fit()
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len > len()`, this has no effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a `char` boundary.
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            assert!(self.is_char_boundary(new_len));
            self.buffer.truncate(new_len);
        }
    }

    /// Removes all text from the string.
    pub fn clear(&mut self) {
        self.buffer.clear()
    }

    /// Extracts a string slice containing the entire string.
    pub fn as_str(&self) -> &str {
        self
    }

    /// Extracts a mutable string slice containing the entire string.
    pub fn as_mut_str(&mut self) -> &mut str {
        self
    }

    /// Consumes the string, turning it into a vector of bytes
    pub fn into_bytes(self) -> Vec<u8> {
        self.buffer.into_vec()
    }

    /// Returns a byte slice of the string's contents
    pub fn as_bytes(&self) -> &[u8] {
        &self.buffer
    }

    /// Removes a char from this String at a byte position and returns it.
    ///
    /// This is an O(n) operation, as it requires copying every element in the
    /// buffer.
    ///
    /// Panics
    /// ------
    ///
    /// Panics if idx is larger than or equal to the String's length, or if it
    /// does not lie on a char boundary.
    #[inline]
    pub fn remove(&mut self, idx: usize) -> char {
        let ch = match self[idx..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = idx + ch.len_utf8();
        let len = self.len();
        unsafe {
            ptr::copy(self.buffer.as_ptr().offset(next as isize),
                      self.buffer.as_mut_ptr().offset(idx as isize),
                      len - next);
            self.buffer.set_len(len - (next - idx));
        }
        ch
    }

    /// Retains only the characters specified by the predicate.
    ///
    /// In other words, remove all characters `c` such that `f(c)` returns `false`.
    /// This method operates in place and preserves the order of the retained
    /// characters.
    ///
    /// # Examples
    ///
    /// ```
    /// # extern crate smallstring;
    /// # use smallstring::SmallString;
    /// # extern crate std;
    /// let mut s: SmallString<[u8;8]> = SmallString::from("f_o_ob_ar");
    ///
    /// s.retain(|c| c != '_');
    ///
    /// assert_eq!(s, SmallString::from("foobar"));
    /// ```
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(char) -> bool
    {
        let len = self.len();
        let mut del_bytes = 0;
        let mut idx = 0;

        while idx < len {
            let ch = unsafe {
                self.slice_unchecked(idx, len).chars().next().unwrap()
            };
            let ch_len = ch.len_utf8();

            if !f(ch) {
                del_bytes += ch_len;
            } else if del_bytes > 0 {
                unsafe {
                    ptr::copy(self.buffer.as_ptr().offset(idx as isize),
                              self.buffer.as_mut_ptr().offset((idx - del_bytes) as isize),
                              ch_len);
                }
            }

            // Point idx to the next char
            idx += ch_len;
        }

        if del_bytes > 0 {
            unsafe { self.buffer.set_len(len - del_bytes); }
        }
    }

    /// Creates a draining iterator that removes the specified range in the string
    /// and yields the removed chars.
    ///
    /// Note: The element range is removed even if the iterator is not
    /// consumed until the end.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # extern crate smallstring;
    /// # use smallstring::SmallString;
    /// # extern crate std;
    /// let mut s: SmallString<[u8;8]> = SmallString::from("α is alpha, β is beta");
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Remove the range up until the β from the string
    /// let t: SmallString = s.drain(..beta_offset).collect();
    /// assert_eq!(t, SmallString::from("α is alpha, "));
    /// assert_eq!(s, SmallString::from("β is beta"));
    ///
    /// // A full range clears the string
    /// s.drain(..);
    /// assert_eq!(s, SmallString::from(""));
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<B>
        where R: RangeBounds<usize>
    {
        use std::ops::Bound::*;
        // Memory safety
        //
        // The String version of Drain does not have the memory safety issues
        // of the vector version. The data is just plain bytes.
        // Because the range removal happens in Drop, if the Drain iterator is leaked,
        // the removal will not happen.
        let len = self.len();
        let start = match range.start_bound() {
            Included(&n) => n,
            Excluded(&n) => n + 1,
            Unbounded => 0,
        };
        let end = match range.end_bound() {
            Included(&n) => n + 1,
            Excluded(&n) => n,
            Unbounded => len,
        };

        // Take out two simultaneous borrows. The &mut String won't be accessed
        // until iteration is over, in Drop.
        let self_ptr = self as *mut _;
        // slicing does the appropriate bounds checks
        let chars_iter = self[start..end].chars();

        Drain {
            start,
            end,
            iter: chars_iter,
            string: self_ptr,
        }
    }
}

impl<B: Array<Item = u8>> std::hash::Hash for SmallString<B> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let s: &str = self;
        s.hash(state)
    }
}

impl<B: Array<Item = u8>> std::cmp::PartialEq for SmallString<B> {
    fn eq(&self, other: &Self) -> bool {
        let (s1, s2): (&str, &str) = (self, other);
        s1 == s2
    }
}

impl<B: Array<Item = u8>> std::cmp::Eq for SmallString<B> {}

impl<'a, B: Array<Item = u8>> PartialEq<SmallString<B>> for &'a str {
    fn eq(&self, other: &SmallString<B>) -> bool {
        *self == (other as &str)
    }
}

impl<B: Array<Item = u8>> std::fmt::Display for SmallString<B> {
    fn fmt(&self, fm: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        let s: &str = SmallString::deref(self);
        s.fmt(fm)
    }
}

impl<B: Array<Item = u8>> std::fmt::Debug for SmallString<B> {
    fn fmt(&self, fm: &mut std::fmt::Formatter) -> std::fmt::Result {
        let s: &str = SmallString::deref(self);
        s.fmt(fm)
    }
}

impl<B: Array<Item = u8>> Deref for SmallString<B> {
    type Target = str;

    fn deref(&self) -> &str {
        // We only allow `buffer` to be created from an existing valid string,
        // so this is safe.
        unsafe { str::from_utf8_unchecked(self.buffer.as_ref()) }
    }
}

impl<B: Array<Item = u8>> DerefMut for SmallString<B> {
    fn deref_mut(&mut self) -> &mut str {
        // We only allow `buffer` to be created from an existing valid string,
        // so this is safe.
        unsafe {
            str::from_utf8_unchecked_mut(self.buffer.as_mut())
        }
    }
}

impl<B: Array<Item = u8>> AsRef<[u8]> for SmallString<B> {
    fn as_ref(&self) -> &[u8] {
        &self.buffer
    }
}

impl<B: Array<Item = u8>> AsRef<str> for SmallString<B> {
    fn as_ref(&self) -> &str {
        self // forward to Deref
    }
}

impl<B: Array<Item = u8>> AsMut<str> for SmallString<B> {
    fn as_mut(&mut self) -> &mut str {
        self // forward to DerefMut
    }
}

impl<B: Array<Item = u8>> Extend<char> for SmallString<B> {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        for ch in iterator {
            self.push(ch);
        }
    }
}

impl<'a, B: Array<Item = u8>> Extend<&'a str> for SmallString<B> {
    fn extend<I: IntoIterator<Item = &'a str>>(&mut self, iter: I) {
        for s in iter {
            self.push_str(s);
        }
    }
}

impl<B: Array<Item = u8>> FromIterator<char> for SmallString<B> {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut buf = SmallString::new();
        buf.extend(iter);
        buf
    }
}

#[cfg(feature = "std")]
impl<B: Array<Item = u8>> AsRef<OsStr> for SmallString<B> {
    fn as_ref(&self) -> &OsStr {
        let s: &str = self.as_ref();
        s.as_ref()
    }
}

impl<B: Array<Item = u8>> Borrow<str> for SmallString<B> {
    fn borrow(&self) -> &str {
        &self
    }
}

impl<'a, B: Array<Item = u8>> From<&'a str> for SmallString<B> {
    fn from(s: &str) -> Self {
        SmallString {
            buffer: SmallVec::from_slice(s.as_bytes()),
        }
    }
}

impl<B: Array<Item = u8>> From<String> for SmallString<B> {
    fn from(s: String) -> Self {
        SmallString {
            buffer: SmallVec::from_vec(s.into_bytes()),
        }
    }
}

impl<B: Array<Item = u8>> From<char> for SmallString<B> {
    fn from(item: char) -> Self {
        let mut buf = SmallString::new();
        buf.push(item);
        buf
    }
}

impl<B: Array<Item = u8>> From<u8> for SmallString<B> {
    fn from(item: u8) -> Self {
        SmallString::from(item as char)
    }
}

impl<'a, B: Array<Item = u8>> From<&'a [u8]> for SmallString<B> {
    fn from(item: &[u8]) -> Self {
        SmallString {
            buffer: SmallVec::from_slice(item)
        }
    }
}

impl<B: Array<Item = u8>> From<SmallString<B>> for String {
    fn from(s: SmallString<B>) -> String {
        unsafe { String::from_utf8_unchecked(s.buffer.into_vec()) }
    }
}

impl<'a, B: Array<Item = u8>> FromIterator<&'a str> for SmallString<B> {
    fn from_iter<I: IntoIterator<Item = &'a str>>(iter: I) -> Self {
        let mut buf = SmallString::new();
        buf.extend(iter);
        buf
    }
}

/// A draining iterator for `SmallString`.
///
/// This struct is created by the [`drain`] method on [`SmallString`]. See its
/// documentation for more.
///
/// [`drain`]: struct.SmallString.html#method.drain
/// [`SmallString`]: struct.SmallString.html
pub struct Drain<'a, B: Array<Item = u8>> {
    /// Will be used as &'a mut String in the destructor
    string: *mut SmallString<B>,
    /// Start of part to remove
    start: usize,
    /// End of part to remove
    end: usize,
    /// Current remaining range to remove
    iter: Chars<'a>,
}

impl<'a, B: Array<Item = u8>> fmt::Debug for Drain<'a, B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Drain { .. }")
    }
}

unsafe impl<'a, B: Array<Item = u8>> Sync for Drain<'a, B> {}
unsafe impl<'a, B: Array<Item = u8>> Send for Drain<'a, B> {}

impl<'a, B: Array<Item = u8>> Drop for Drain<'a, B> {
    fn drop(&mut self) {
        unsafe {
            // "Reaffirm" the bounds checks to avoid panic code being
            // inserted again.
            let self_str = &mut (*self.string);
            if self.start <= self.end && self.end <= self_str.len() {
                let len = self_str.len();
                ptr::copy(self_str.buffer.as_ptr().add(self.end),
                        self_str.buffer.as_mut_ptr().add(self.start),
                        self.end - self.start);
                self_str.buffer.set_len(len - (self.end - self.start));
            }
        }
    }
}

impl<'a, B: Array<Item = u8>> Iterator for Drain<'a, B> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, B: Array<Item = u8>> DoubleEndedIterator for Drain<'a, B> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl<'a, B: Array<Item = u8>> FusedIterator for Drain<'a, B> {}
