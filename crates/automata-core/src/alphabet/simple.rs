#![allow(missing_docs)]

use std::collections::VecDeque;

use itertools::Itertools;

use crate::show::Show;

use super::{Alphabet, Expression, Matcher, Symbol};

pub trait SimpleAlphabet: Alphabet
where
    Self: Alphabet<Expression = <Self as Alphabet>::Symbol>,
{
    fn express(&self, sym: Self::Symbol) -> &Self::Expression;
    fn try_nth(&self, pos: usize) -> Option<Self::Symbol>;
    fn nth(&self, pos: usize) -> Self::Symbol {
        self.try_nth(pos).unwrap()
    }
    fn try_position(&self, symbol: Self::Symbol) -> Option<usize>;
    fn position(&self, symbol: Self::Symbol) -> usize {
        self.try_position(symbol).unwrap()
    }
}

/// Represents an alphabet where a [`Symbol`] is just a single `char`.
///
/// # Example
/// Assume we have a [`CharAlphabet`] over the symbols 'a' and 'b'. Then a **symbol** would be just one of these
/// characters, e.g. 'a'. This is used to label transitions in a transition system or automaton.
/// Now an **expression** would also be just a single character, e.g. 'a'. Then such an expression is
/// matched by a symbol if the expression equals the symbol.
#[derive(Clone, Hash, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub struct CharAlphabet(pub(crate) Vec<char>);

impl CharAlphabet {
    /// Creates a new [`CharAlphabet`] alphabet of the given size. The symbols are just the first `size` letters
    /// of the alphabet, i.e. 'a' to 'z'.
    pub fn of_size(size: usize) -> Self {
        assert!(size < 26, "Alphabet is too large");
        Self((0..size).map(|i| (b'a' + i as u8) as char).collect())
    }
}

impl std::ops::Index<usize> for CharAlphabet {
    type Output = char;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl From<Vec<char>> for CharAlphabet {
    fn from(value: Vec<char>) -> Self {
        Self(value)
    }
}

impl FromIterator<char> for CharAlphabet {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        Self(iter.into_iter().unique().sorted().collect())
    }
}

impl CharAlphabet {
    /// Creates a new [`CharAlphabet`] alphabet from an iterator over the symbols.
    pub fn new(symbols: Vec<char>) -> Self {
        Self(symbols)
    }
}

impl Matcher<Self> for char {
    fn matches(&self, expression: &Self) -> bool {
        self == expression
    }
}

impl Expression for char {
    type S = Self;
    type SymbolsIter<'this>
        = std::iter::Once<Self>
    where
        Self: 'this;
    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn for_each<F: Fn(Self)>(&self, f: F) {
        (f)(*self)
    }

    fn matched_by(&self, symbol: Self) -> bool {
        self == &symbol
    }
}

impl Alphabet for CharAlphabet {
    type Symbol = char;

    type Expression = char;

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, char>>
    where
        Self: 'this;

    fn size(&self) -> usize {
        self.0.len()
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.contains(&symbol)
    }

    #[inline(always)]
    fn search_edge<X>(
        map: &crate::math::OrderedMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        *self
            .0
            .iter()
            .find(|c| c == &&symbol)
            .expect("symbol does not exist")
    }
}

impl SimpleAlphabet for CharAlphabet {
    fn express(&self, sym: Self::Symbol) -> &Self::Expression {
        self.0
            .iter()
            .find(|c| c == &&sym)
            .expect("cannot express unavailable symbol!")
    }

    fn try_nth(&self, pos: usize) -> Option<Self::Symbol> {
        self.0.get(pos).cloned()
    }

    fn try_position(&self, symbol: Self::Symbol) -> Option<usize> {
        self.0.iter().position(|x| symbol.eq(x))
    }
}

/// An alphabet of fixed arity, uses const generics. This is more seen as a test
/// since the performance gains (at least for simple operations like runs) is
/// negligible.
#[derive(Clone, Debug)]
pub struct Fixed<S: Symbol, const N: usize>([S; N]);

impl Matcher<Self> for usize {
    fn matches(&self, expression: &Self) -> bool {
        self == expression
    }
}

impl Expression for usize {
    type S = Self;
    type SymbolsIter<'this>
        = std::iter::Once<Self>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn matched_by(&self, symbol: Self) -> bool {
        *self == symbol
    }
}

impl<S: Symbol, const N: usize> Fixed<S, N> {
    /// Create a new [`Fixed`] alphabet from a slice of length `N`.
    pub fn from(symbols: [S; N]) -> Self {
        Self(symbols)
    }
}

impl<S: Symbol + Matcher<S> + Expression<S = S>, const N: usize> Alphabet for Fixed<S, N> {
    type Symbol = S;

    type Expression = S;

    fn search_edge<X>(
        map: &crate::math::OrderedMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    fn size(&self) -> usize {
        N
    }

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, S>>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.contains(&symbol)
    }

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        *self
            .0
            .iter()
            .find(|c| c == &&symbol)
            .expect("symbol does not exist")
    }
}

/// A [`CharAlphabet`] alphabet where symbols can be inverted. This means that a symbol can either be
/// appended to the end of a word or prepended to the beginning of a word. This is used to
/// implement the [`Directional`] alphabet.
#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct InvertibleChar(char, bool);

impl InvertibleChar {
    /// Multiplies the given word with this symbol. If the symbol is inverted, then it is prepended
    /// to the word, otherwise it is appended.
    pub fn mul(&self, word: &mut VecDeque<char>) {
        if self.1 {
            word.push_front(self.0)
        } else {
            word.push_back(self.0)
        }
    }

    /// Returns true if this symbol is inverted.
    pub fn is_inverted(&self) -> bool {
        self.1
    }
}

impl Matcher<Self> for InvertibleChar {
    fn matches(&self, expression: &Self) -> bool {
        self == expression
    }
}

impl Expression for InvertibleChar {
    type S = Self;
    type SymbolsIter<'this>
        = std::iter::Once<Self>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        std::iter::once(*self)
    }
    fn overlaps(&self, other: &Self) -> bool {
        self == other
    }

    fn matched_by(&self, symbol: Self) -> bool {
        *self == symbol
    }
}

impl Show for InvertibleChar {
    fn show(&self) -> String {
        format!("{}{}", self.0, if self.1 { "\u{0303}" } else { "" })
    }

    fn show_collection<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> String
    where
        Self: 'a,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("'{}'", iter.into_iter().rev().map(|c| c.show()).join(""))
    }
}

/// A [`CharAlphabet`] alphabet where each symbol can be inverted. This means that a symbol can either be
/// appended to the end of a word or prepended to the beginning of a word. This can be used to
/// represent two-sided congruences.
#[derive(Clone, Debug)]
pub struct Directional(Vec<InvertibleChar>);

impl FromIterator<char> for Directional {
    fn from_iter<I: IntoIterator<Item = char>>(iter: I) -> Self {
        let mut v = vec![];
        for sym in iter {
            v.push(InvertibleChar(sym, false));
            v.push(InvertibleChar(sym, true));
        }
        Self(v)
    }
}

impl Directional {
    /// Takes a 'usual' alphabet and turns every symbol into an [`InvertibleChar`], that is every
    /// char can now be an append- or a prepend-symbol.
    pub fn from_alphabet<A: std::borrow::Borrow<CharAlphabet>>(alphabet: A) -> Self {
        Self::from_iter(alphabet.borrow().universe())
    }
}

impl Alphabet for Directional {
    type Symbol = InvertibleChar;

    type Expression = InvertibleChar;

    fn search_edge<X>(
        map: &crate::math::OrderedMap<Self::Expression, X>,
        sym: Self::Symbol,
    ) -> Option<(&Self::Expression, &X)> {
        map.get_key_value(&sym)
    }

    fn size(&self) -> usize {
        self.0.len()
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        left == right
    }

    type Universe<'this>
        = std::iter::Cloned<std::slice::Iter<'this, InvertibleChar>>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.0.iter().cloned()
    }

    fn contains(&self, symbol: Self::Symbol) -> bool {
        self.0.contains(&symbol)
    }

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        *self
            .0
            .iter()
            .find(|c| c == &&symbol)
            .expect("symbol does not exist")
    }
}

#[cfg(test)]
mod tests {
    use super::Alphabet;
    use super::{CharAlphabet, Directional};
    use itertools::Itertools;

    #[test]
    fn bialphabet() {
        let alph = CharAlphabet::from_iter(['a', 'b', 'c']);
        let bi = Directional::from_alphabet(alph);
        assert_eq!(bi.universe().collect_vec().len(), 6);
    }
}
