use std::collections::VecDeque;

use itertools::Itertools;

use crate::{alphabet::Symbol, show::Show};

use super::{Concat, PeriodicOmegaWord, Repeat, Word, omega::OmegaIteration};

/// A finite word is a [`Word`] that has a finite length.
pub trait FiniteWord: Word {
    /// Type for an iterator over the symbols making up the word.
    type Symbols<'this>: Iterator<Item = Self::Symbol>
    where
        Self: 'this;

    /// Returns an iterator over the symbols of the word.
    fn symbols(&self) -> Self::Symbols<'_>;

    /// Appends the given [`Word`] to the end of this word. Note, that the appended
    /// suffix may be finite or infinite.
    fn append<W: Word<Symbol = Self::Symbol>>(self, suffix: W) -> Concat<Self, W>
    where
        Self: Sized,
    {
        Concat(self, suffix)
    }

    /// Checks if the given word is equal to this word. Note, that this operation only makes sense
    /// when both words are finite.
    fn finite_word_equals<W: FiniteWord<Symbol = Self::Symbol>>(&self, other: W) -> bool {
        assert!(W::FINITE);
        self.len() == other.len() && self.symbols().zip(other.symbols()).all(|(a, b)| a == b)
    }

    /// Compares the finite word self
    fn length_lexicographic_ord<W: FiniteWord<Symbol = Self::Symbol>>(
        &self,
        other: W,
    ) -> std::cmp::Ordering {
        assert!(W::FINITE);
        self.len()
            .cmp(&other.len())
            .then(self.symbols().cmp(other.symbols()))
    }

    /// Prepends the given `prefix` to the beginning of this word. This operation only works if
    /// the prefix is finite.
    fn prepend<W: FiniteWord<Symbol = Self::Symbol>>(self, prefix: W) -> Concat<W, Self>
    where
        Self: Sized,
    {
        Concat(prefix, self)
    }

    /// Consumes `self` and collects the symbols into a [`Vec`].
    fn into_vec(self) -> Vec<Self::Symbol>
    where
        Self: Sized,
    {
        self.collect_vec()
    }

    /// Collects the symbols making up `self` into a vector.
    fn collect_vec(&self) -> Vec<Self::Symbol> {
        self.symbols().collect()
    }

    /// Collects the symbols making up `self` into a [`VecDeque`].
    fn collect_deque(&self) -> VecDeque<Self::Symbol> {
        VecDeque::from(self.collect_vec())
    }

    /// Repeat self the given number of times.
    fn repeat(self, times: usize) -> Repeat<Self>
    where
        Self: Sized,
    {
        Repeat::new(self, times)
    }

    /// Builds the [`PeriodicOmegaWord`] word that is the omega power of this word, i.e. if
    /// `self` is the word `u`, then the result is the word `u^ω` = `u u u u ...`.
    /// Panics if `self` is empty as the operation is not defined in that case.
    fn omega_power(&self) -> PeriodicOmegaWord<Self::Symbol> {
        assert!(
            !self.is_empty(),
            "Omega iteration of an empty word is undefined!"
        );
        PeriodicOmegaWord::new(self)
    }

    /// Provides a thin wrapper around a finite word that represents the omega (infinite)
    /// iteration of it.
    fn omega_iteration(self) -> OmegaIteration<Self>
    where
        Self: Sized,
    {
        assert!(
            !self.is_empty(),
            "Omega iteration of an empty word is undefined!"
        );
        OmegaIteration::new(self)
    }

    /// Gives the length of the word, i.e. the number of symbols.
    fn len(&self) -> usize {
        self.symbols().count()
    }

    /// Returns the `n`-th symbol of the word from the back.
    ///
    /// # Example
    /// ```
    /// use automata_core::word::FiniteWord;
    ///
    /// let word = "abc";
    ///
    /// assert_eq!(word.nth_back(0), Some('c'));
    /// assert_eq!(word.nth_back(1), Some('b'));
    /// assert_eq!(word.nth_back(2), Some('a'));
    /// ```
    fn nth_back(&self, pos: usize) -> Option<Self::Symbol> {
        self.nth(self.len() - pos - 1)
    }

    /// Returns `true` if the word is empty, i.e. has no symbols.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Converts the word to a string. This is only possible if the the symbols implement
    /// the [`Show`] trait.
    fn as_string(&self) -> String
    where
        Self::Symbol: Show,
    {
        let out = self.symbols().map(|a| a.show()).join("");
        if out.is_empty() { "ε".into() } else { out }
    }
}

impl<S: Symbol, const N: usize> FiniteWord for [S; N] {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn into_vec(self) -> Vec<S> {
        self.collect_vec()
    }

    fn symbols(&self) -> Self::Symbols<'_> {
        self.iter().cloned()
    }
}

impl<S: Symbol, const N: usize> Word for [S; N] {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<S> {
        self.get(position).cloned()
    }
}

impl<S: Symbol, Fw: FiniteWord<Symbol = S> + ?Sized> FiniteWord for &Fw {
    type Symbols<'this>
        = Fw::Symbols<'this>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        (*self).symbols()
    }

    fn len(&self) -> usize {
        (*self).len()
    }
    fn collect_vec(&self) -> Vec<S> {
        (*self).collect_vec()
    }
}

impl<S: Symbol> Word for VecDeque<S> {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<S> {
        if position < self.len() {
            Some(self[position])
        } else {
            None
        }
    }
}

impl<S: Symbol> FiniteWord for VecDeque<S> {
    type Symbols<'this>
        = std::iter::Cloned<std::collections::vec_deque::Iter<'this, S>>
    where
        Self: 'this;

    fn into_vec(self) -> Vec<S> {
        self.into()
    }

    fn symbols(&self) -> Self::Symbols<'_> {
        self.iter().cloned()
    }
}

impl Word for str {
    type Symbol = char;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<char> {
        self.chars().nth(position)
    }
}

impl FiniteWord for str {
    type Symbols<'this> = std::str::Chars<'this>;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.chars()
    }

    fn len(&self) -> usize {
        self.len()
    }
    fn collect_vec(&self) -> Vec<char> {
        self.chars().collect()
    }
}

impl Word for String {
    type Symbol = char;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<char> {
        self.chars().nth(position)
    }
}

impl FiniteWord for String {
    fn collect_vec(&self) -> Vec<char> {
        self.chars().collect()
    }

    fn len(&self) -> usize {
        self.len()
    }

    type Symbols<'this>
        = std::str::Chars<'this>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.chars()
    }

    fn into_vec(self) -> Vec<char> {
        self.chars().collect()
    }
}

impl<S: Symbol> Word for Vec<S> {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<S> {
        if position < self.len() {
            Some(self[position])
        } else {
            None
        }
    }
}
impl<S: Symbol> FiniteWord for Vec<S> {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.iter().cloned()
    }

    fn collect_vec(&self) -> Self {
        self.clone()
    }
    fn into_vec(self) -> Self {
        self
    }

    fn len(&self) -> usize {
        self.len()
    }
}

impl<S: Symbol> Word for [S] {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<S> {
        if position < self.len() {
            Some(self[position])
        } else {
            None
        }
    }
}
impl<S: Symbol> FiniteWord for [S] {
    type Symbols<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        self.iter().cloned()
    }

    fn collect_vec(&self) -> Vec<S> {
        self.to_vec()
    }

    fn len(&self) -> usize {
        self.len()
    }
}
