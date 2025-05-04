use itertools::Itertools;
use std::{fmt::Debug, marker::PhantomData};
use thiserror::Error;

use crate::{alphabet::Symbol, show::Show};

use super::{FiniteWord, Word};

/// An omega word is an infinite word that can be indexed by a `usize`. We assume that all
/// omega words can be represented as a concatenation of a finite prefix which we call spoke
/// and a finite loop which we call cycle. The loop index is the length of the spoke.
///
/// # Normalization
/// Omega words can be brought into a normalized form, where the prefix/spoke is rolled into
/// the loop as far as possible. Specifically, this means that the word `w = abca(caca)^𝜔` can be
/// transformed into the equivalent omega word `ab(caca)^𝜔`. Subsequently, we normalize the
/// looping/cycling part by attempting to find a factor such that the loop is some repetition
/// of the factor. In this instance, that would mean to normalize `w` into `ab(ca)^𝜔`.
///
/// Normalization is always possible and leads to a minimal representation of an omega word.
/// This representation is unique and can be computed in polynomial time.
///
/// # Equality testing
/// Most implementors of `OmegaWord` should also implement `PartialEq`/`Eq`. Note, that this
/// represents syntactical/structural equality. To test for syntactic equality (i.e. equality
/// of the represented word itself), the method [`OmegaWord::omega_word_equals()`] should be used. This
/// method first normalizes the words in question and subsequently compares the loop and spoke.
///
/// # Example
/// ```
/// use automata_core::{upw, word::OmegaWord};
///
/// let word = upw!("abc", "def"); // represents abc(def)^𝜔 = abcdefdefdef...
/// assert_eq!(word.loop_index(), 3);
/// assert_eq!(word.cycle_len(), 3);
/// ```
pub trait OmegaWord: Word {
    /// The type of finite word representing the spoke, i.e. the finite prefix of the word
    /// before the loop index.  
    type Spoke<'this>: FiniteWord<Symbol = Self::Symbol>
    where
        Self: 'this;
    /// The type of finite word that represents the cycle of th omega word, i.e. the
    /// finite loop that is repeated infinitely often.
    type Cycle<'this>: FiniteWord<Symbol = Self::Symbol>
    where
        Self: 'this;

    /// Returns a normalized ultimately periodic word that is equal to `self`. This is done by
    /// first folding the prefix into the loop as far as possible and then deduplicating the
    /// loop.
    ///
    /// The representation returned by this method is unique and minimal for `self`. It is computed
    /// in polynomial time.
    ///
    /// # Example
    /// ```
    /// use automata_core::{upw, word::{FiniteWord, OmegaWord}};
    ///
    /// let word = upw!("abac", "acac");
    /// assert!(word.spoke().finite_word_equals("ab"));
    /// assert!(word.cycle().finite_word_equals("ac"));
    /// ```
    fn reduced(&self) -> ReducedOmegaWord<Self::Symbol> {
        ReducedOmegaWord::ultimately_periodic(self.spoke(), self.cycle())
    }

    /// Tests whether `self` is *semantically* equal to `other`. To see the difference compared to syntactic
    /// equality, consider the exampe below.
    /// ```
    /// use automata_core::{upw, word::{FiniteWord, OmegaWord, Word}};
    ///
    /// let word = upw!("a"); // represents the periodic omega word a^𝜔 = aaa...
    /// let offset1 = word.skip(1); // the word obtained by skipping the first symbol of `word`
    /// let offset2 = word.skip(2);
    ///
    /// assert!(offset1 != offset2); // two different offsets are syntactically distinct
    /// assert!(offset1.omega_word_equals(offset2)); // but they are semantically equal
    /// ```
    fn omega_word_equals<W: OmegaWord<Symbol = Self::Symbol>>(&self, other: W) -> bool {
        assert!(!W::FINITE);
        self.reduced() == other.reduced()
    }

    /// Returns the spoke of the word, i.e. the finite prefix of the word before the loop index.
    fn spoke(&self) -> Self::Spoke<'_>;
    /// Returns the cycle of the word, i.e. the finite loop that is repeated infinitely often.
    fn cycle(&self) -> Self::Cycle<'_>;

    /// Returns a vector consisting of the symbols making up the cycle of `self`. This simply collects
    /// whatever symbols make up [`OmegaWord::cycle()`];
    fn cycle_vec(&self) -> Vec<Self::Symbol> {
        self.cycle().into_vec()
    }

    /// Returns a vector consisting of the symbols making up the spoke of `self`. This simply collects
    /// whatever symbols make up [`OmegaWord::spoke()`];
    fn spoke_vec(&self) -> Vec<Self::Symbol> {
        self.spoke().collect_vec()
    }

    /// Returns the loop index of the word, i.e. the length of the spoke. This can be zero if
    /// the word is periodic.
    fn loop_index(&self) -> usize {
        self.spoke().len()
    }

    /// Gives the length of the cycle of the word, i.e. the length of the loop that is repeated
    /// infinitely often. Note that if the word is not normalized, then there might be a shorter
    /// representation of the cycle that is repeated, e.g. a cycle of `aaa` could also be
    /// represented by the cycle `a`.
    fn cycle_len(&self) -> usize {
        self.cycle().len()
    }

    /// Gives the length of the spoke of the word, so the number of symbols before the loop
    /// is entered.
    fn spoke_len(&self) -> usize {
        self.spoke().len()
    }

    /// Returns the combined (flat) length of `self`. Note, that since
    /// `self` is infinite, this is a length of the representation of
    /// `self` as an ultimately periodic word.
    /// This essentially just adds the [`Self::spoke_len`] to the
    /// [`Self::cycle_len`].
    fn combined_len(&self) -> usize {
        self.cycle_len() + self.spoke_len()
    }
}

impl<W: OmegaWord> OmegaWord for &W {
    type Spoke<'this>
        = W::Spoke<'this>
    where
        Self: 'this;

    type Cycle<'this>
        = W::Cycle<'this>
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        W::spoke(self)
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        W::cycle(self)
    }
}

fn deduplicate_inplace<S: Eq>(input: &mut Vec<S>) {
    assert!(!input.is_empty());

    for i in 1..=(input.len() / 2) {
        // for a word w of length n, if th first n-i symbols of w are equal to the
        // last n-i symbols of w, then w is periodic with period i
        if input.len() % i == 0 && input[..input.len() - i] == input[i..] {
            input.truncate(i);
            return;
        }
    }
}

fn deduplicate<S: Eq>(input: Vec<S>) -> Vec<S> {
    let mut input = input;
    deduplicate_inplace(&mut input);
    input
}

/// A periodic omega word has no finite prefix and consists only of a finite loop that is
/// repeated infinitely often. Note, that the loop cannot be empty.
/// TODO: make non-empty word into a new type
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct PeriodicOmegaWord<S> {
    representation: Vec<S>,
}

impl<S: Symbol> TryFrom<ReducedOmegaWord<S>> for PeriodicOmegaWord<S> {
    type Error = ();
    fn try_from(value: ReducedOmegaWord<S>) -> Result<Self, Self::Error> {
        if value.loop_index() > 0 {
            Err(())
        } else {
            Ok(Self {
                representation: value.word,
            })
        }
    }
}

impl<S: Show> Show for PeriodicOmegaWord<S> {
    fn show(&self) -> String {
        self.representation.show()
    }
}

impl<S: Symbol> From<PeriodicOmegaWord<S>> for ReducedOmegaWord<S> {
    fn from(value: PeriodicOmegaWord<S>) -> Self {
        Self::periodic(value.representation)
    }
}
impl<S: Symbol> From<&PeriodicOmegaWord<S>> for ReducedOmegaWord<S> {
    fn from(value: &PeriodicOmegaWord<S>) -> Self {
        Self::periodic(value.representation.clone())
    }
}

impl<S: Symbol> From<&Self> for ReducedOmegaWord<S> {
    fn from(value: &Self) -> Self {
        Self::ultimately_periodic(value.spoke(), value.cycle())
    }
}

impl<S: Symbol> PeriodicOmegaWord<S> {
    /// Creates a new periodic omega word from a finite word. The word must not be empty and
    /// it is deduplicated.
    ///
    /// # Example
    /// ```
    /// use automata_core::{upw, word::{FiniteWord, OmegaWord}};
    ///
    /// let word = upw!("abcabcabc");
    /// assert_eq!(word.cycle_len(), 3);
    /// assert_eq!(word.loop_index(), 0);
    /// assert!(word.spoke().is_empty());
    /// assert!(word.cycle().finite_word_equals("abc"));
    /// ```
    pub fn new<W: FiniteWord<Symbol = S>>(word: W) -> Self {
        let mut representation = word.collect_vec();
        deduplicate_inplace(&mut representation);
        Self { representation }
    }

    /// Gives a reference to the underlying representation of the word.
    pub fn representation(&self) -> &[S] {
        &self.representation
    }

    /// Gives a mutable reference to the underlying representation of the word.
    pub fn representation_mut(&mut self) -> &mut [S] {
        &mut self.representation
    }
}

impl<S: Symbol> Word for PeriodicOmegaWord<S> {
    type Symbol = S;
    const FINITE: bool = false;
    fn nth(&self, position: usize) -> Option<S> {
        self.representation
            .get(position % self.representation.len())
            .copied()
    }
}
impl<S: Symbol> OmegaWord for PeriodicOmegaWord<S> {
    fn loop_index(&self) -> usize {
        0
    }

    type Spoke<'this>
        = &'this [S]
    where
        Self: 'this;

    type Cycle<'this>
        = &'this [S]
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        self.representation[..self.loop_index()].as_ref()
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        self.representation[self.loop_index()..].as_ref()
    }
}

/// Represents a reduced omega word. For ultimately periodic words, this means we
/// try to roll the prefix part into the looping part and deduplicate the looping
/// part. For periodic words, we just deduplicate the looping part.
///
/// Crucially, an instance of this struct will always be in reduced form. Specifically,
/// this means that there is no shorter representation of the omega word in the form
/// of a finite spoke and finite, non-empty cycle.
///
/// The reduced representation can be computed in polynomial time and it is unique.
/// We can compute it by calling [`OmegaWord::reduced()`] and it is possible to
/// verify whether an instance of `Self` is normalized through the [`ReducedOmegaWord::is_reduced()`]
/// method.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ReducedOmegaWord<S> {
    pub(super) word: Vec<S>,
    pub(super) loop_index: usize,
}

impl<S: Symbol> Show for ReducedOmegaWord<S> {
    fn show(&self) -> String {
        format!(
            "{},({})",
            self.word[0..self.loop_index]
                .iter()
                .map(|chr| chr.show())
                .join(""),
            self.word[self.loop_index..]
                .iter()
                .map(|chr| chr.show())
                .join("")
        )
    }
}

impl<S: Symbol> Word for ReducedOmegaWord<S> {
    type Symbol = S;
    const FINITE: bool = false;
    fn nth(&self, position: usize) -> Option<S> {
        if position >= self.word.len() {
            let loop_position = (position - self.loop_index) % self.cycle_len();
            self.word.nth(self.loop_index + loop_position)
        } else {
            self.word.nth(position)
        }
    }
}
impl<S: Symbol> OmegaWord for ReducedOmegaWord<S> {
    fn loop_index(&self) -> usize {
        self.loop_index
    }

    type Spoke<'this>
        = &'this [S]
    where
        Self: 'this;

    type Cycle<'this>
        = &'this [S]
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        self.word[..self.loop_index].as_ref()
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        self.word[self.loop_index..].as_ref()
    }
}

impl<S: Symbol> ReducedOmegaWord<S> {
    /// Returns `true` if and only if `self` is already normalized. This is done by
    /// computing the normalization of `self` and then comparing structural equality.
    ///
    /// # Example
    /// ```
    /// use automata_core::{upw, word::{FiniteWord, OmegaWord, ReducedOmegaWord}};
    ///
    /// let non_normalized = ReducedOmegaWord::from_raw_parts(vec!['a', 'a'], 0);
    /// assert!(!non_normalized.is_reduced()); // the constructed word is not normalized
    /// let normalized = non_normalized.reduced();
    /// assert!(normalized.is_reduced()); // the normalization is normalized
    /// assert!(normalized != non_normalized); // they are not syntactically equal
    /// assert!(normalized.omega_word_equals(non_normalized)); // but they are semantically equal
    /// ```
    pub fn is_reduced(&self) -> bool {
        self.reduced() == *self
    }

    /// Creates a new instance from the given representation and loop index.
    pub fn from_raw_parts(repr: Vec<S>, loop_index: usize) -> Self {
        Self {
            word: repr,
            loop_index,
        }
    }

    /// Creates a new reduced omega word from a finite word. The input is deduplicated.
    pub fn periodic<W: FiniteWord<Symbol = S>>(representation: W) -> Self {
        let representation = deduplicate(representation.collect_vec());
        Self {
            word: representation,
            loop_index: 0,
        }
    }

    /// Removes the first symbol from the word. If the spoke is not empty (i.e. the loop index
    /// is greater than zero), we simply pop the first symbol of the prefix and decrease the
    /// loop index by one. Otherwise, if the spoke is empty, then the loop is rotated
    /// by one symbol.
    pub fn pop_front(&mut self) -> S {
        assert!(self.loop_index < self.word.len());
        if self.loop_index() > 0 {
            let mut it = self.word.iter().cloned();
            let out = it.next().expect("infinite word!");
            self.word = it.collect();
            self.loop_index -= 1;
            out
        } else {
            let out = *self
                .cycle()
                .first()
                .expect("this is an infinite word, loop must be non-empty");
            self.word.rotate_left(1);
            out
        }
    }

    /// Creates a new reduced omega word from a finite word representing the spoke and a finite
    /// word representing the cycle. The spoke must not be empty.
    pub fn ultimately_periodic<Spoke: FiniteWord<Symbol = S>, Cycle: FiniteWord<Symbol = S>>(
        spoke: Spoke,
        cycle: Cycle,
    ) -> Self {
        assert!(
            !cycle.is_empty(),
            "ultimately periodic words cannot have empty cycle"
        );

        // see how far we can roll the the loop index back.
        let roll_in = (0..spoke.len())
            .take_while(|i| spoke.nth_back(*i) == cycle.nth_back(*i % cycle.len()))
            .max()
            .map(|x| x + 1)
            .unwrap_or(0);

        let mut loop_representation = cycle.collect_vec();
        loop_representation.rotate_right(roll_in % cycle.len());
        deduplicate_inplace(&mut loop_representation);

        let mut representation = spoke.collect_vec();
        representation.truncate(spoke.len().saturating_sub(roll_in));
        let loop_index = representation.len();
        representation.extend(loop_representation);

        let out = Self {
            word: representation,
            loop_index,
        };
        if cfg!(debug_assertions) {
            for (i, a) in spoke.symbols().enumerate() {
                assert_eq!(out.nth(i), Some(a));
            }
            for (i, a) in cycle.symbols().enumerate() {
                assert_eq!(out.nth(spoke.len() + i), Some(a));
            }
        }
        out
    }

    /// Returns a reference to the underlying raw representation.
    pub fn raw_word(&self) -> &[S] {
        &self.word
    }

    /// Gives the first symbol of the word.
    pub fn first(&self) -> Option<S> {
        self.word.first()
    }
}

impl ReducedOmegaWord<char> {
    /// Tries to construct an instance of a [`ReducedOmegaWord`] with
    /// symbols of type `char` from the given `&str`.
    pub fn try_from_str(value: &str) -> Result<Self, ReducedParseError> {
        match value.split_once(',') {
            None => {
                if value.is_empty() {
                    Err(ReducedParseError::Empty)
                } else {
                    Ok(Self::periodic(value.trim()))
                }
            }
            Some((initial, repeating)) => {
                if repeating.is_empty() {
                    Err(ReducedParseError::EmptyLoop)
                } else {
                    if repeating.contains(',') {
                        return Err(ReducedParseError::TooManyCommas);
                    }
                    let initial = initial.trim();
                    let repeating = repeating.trim();
                    Ok(Self::ultimately_periodic(initial, repeating))
                }
            }
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Epsilon<S>(PhantomData<S>);

impl<S: Symbol> Word for Epsilon<S> {
    type Symbol = S;
    const FINITE: bool = true;
    fn nth(&self, _position: usize) -> Option<S> {
        None
    }
}

impl<S: Symbol> FiniteWord for Epsilon<S> {
    type Symbols<'this>
        = std::iter::Empty<S>
    where
        Self: 'this;

    fn symbols(&self) -> Self::Symbols<'_> {
        std::iter::empty()
    }

    fn collect_vec(&self) -> Vec<S> {
        vec![]
    }

    fn len(&self) -> usize {
        0
    }
}

/// Represents the omega iteration of a (non-empty) finite word.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct OmegaIteration<W>(W);

impl<W: FiniteWord> OmegaIteration<W> {
    /// Iterate the given finite word `from`, panics if the word is empty.
    pub fn new(from: W) -> Self {
        assert!(!from.is_empty(), "Cannot iterate an empty word");
        Self(from)
    }
}

impl<W: FiniteWord> Word for OmegaIteration<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = false;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        self.0.nth(position % self.0.len())
    }
}

impl<W: FiniteWord> OmegaWord for OmegaIteration<W> {
    type Spoke<'this>
        = Epsilon<W::Symbol>
    where
        Self: 'this;

    type Cycle<'this>
        = &'this W
    where
        Self: 'this;

    fn spoke(&self) -> Self::Spoke<'_> {
        Epsilon(PhantomData)
    }

    fn cycle(&self) -> Self::Cycle<'_> {
        &self.0
    }
}

/// Represents the types of errors that can occur when parsing a reduced word from a string.
#[derive(Debug, Clone, Eq, PartialEq, Error)]
pub enum ReducedParseError {
    /// The word is empty.
    #[error("cannot parse an empty omega word")]
    Empty,
    /// The looping part of the word is empty.
    #[error("the looping part of an omega word may not be empty")]
    EmptyLoop,
    /// The word contains too many commas, when it should contain at most one.
    #[error("too many commas (more than one) in the omega word")]
    TooManyCommas,
}

impl<S: Show> Debug for ReducedOmegaWord<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.loop_index == 0 {
            write!(f, "({})𝜔", self.word.iter().map(|sym| sym.show()).join(""))
        } else {
            write!(
                f,
                "{}, ({})𝜔",
                self.word[..self.loop_index]
                    .iter()
                    .map(|sym| sym.show())
                    .join(""),
                self.word[self.loop_index..]
                    .iter()
                    .map(|sym| sym.show())
                    .join("")
            )
        }
    }
}

impl<S: Show> Debug for PeriodicOmegaWord<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({})𝜔",
            self.representation.iter().map(|sym| sym.show()).join("")
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::word::{FiniteWord, OmegaWord, ReducedOmegaWord, omega::deduplicate};

    use super::deduplicate_inplace;

    #[test]
    fn parse_reduced() {
        let repr = "abab";
        let nupw = super::ReducedOmegaWord::try_from_str(repr).unwrap();
        let mut start = vec!['a', 'b', 'a', 'b'];
        deduplicate_inplace(&mut start);
        assert_eq!(start, vec!['a', 'b']);
        assert_eq!(nupw.word, vec!['a', 'b']);
    }

    #[test]
    fn deduplication() {
        let input = vec![1, 2, 3, 1, 2, 3];
        assert_eq!(deduplicate(input), vec![1, 2, 3]);

        let input = vec![1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2];
        assert_eq!(deduplicate(input), vec![1, 2]);

        let input = vec![1, 2, 3, 1, 2, 3, 1, 2, 3];
        assert_eq!(deduplicate(input), vec![1, 2, 3]);
    }

    #[test]
    fn normalizing_upws() {
        let reduced = super::ReducedOmegaWord::ultimately_periodic("aaaaaaa", "aaaaaaaaa");
        assert_eq!(reduced.word, vec!['a']);
        assert_eq!(
            ReducedOmegaWord::ultimately_periodic("aaaaaaaaa", "a").word,
            vec!['a']
        );
    }

    #[test]
    fn word_equality() {
        let word = crate::upw!("abac", "acac");
        assert!(word.spoke().finite_word_equals("ab"));
        assert!(word.cycle().finite_word_equals("ac"));
    }
}
