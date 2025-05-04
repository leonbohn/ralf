use std::{
    borrow::Borrow,
    cell::RefCell,
    collections::{BTreeSet, VecDeque},
    fmt::Debug,
    hash::Hash,
};

use crate::{passive::dpainf::iteration_consistency_conflicts, prefixtree::prefix_tree};
use automata::core::alphabet::{Alphabet, CharAlphabet, Symbol};
use automata::core::math;
use automata::core::word::{ReducedOmegaWord, Word};
use itertools::Itertools;
use tracing::{debug, trace};

use super::dpainf::{SeparatesIdempotents, dpainf, prefix_consistency_conflicts};

mod split;
pub use split::{ClassOmegaSample, SplitOmegaSample};

mod omega;
pub use omega::{OmegaSampleParseError, PeriodicOmegaSample};

mod finite;
pub use finite::FiniteSampleParseError;

mod canonic_coloring;

pub trait Sample<A: Alphabet> {
    type Word: Word<Symbol = A::Symbol>;
    type PositiveIter<'this>: Iterator<Item = &'this Self::Word>
    where
        Self: 'this,
        Self::Word: 'this;
    type NegativeIter<'this>: Iterator<Item = &'this Self::Word>
    where
        Self: 'this,
        Self::Word: 'this;
    const FINITE: bool;
    fn positive(&self) -> Self::PositiveIter<'_>;
    fn negative(&self) -> Self::NegativeIter<'_>;
    fn words(&self) -> itertools::Interleave<Self::PositiveIter<'_>, Self::NegativeIter<'_>> {
        self.positive().interleave(self.negative())
    }
    fn classified_words<'a>(&'a self) -> impl Iterator<Item = (&'a Self::Word, bool)>
    where
        Self::Word: 'a,
    {
        self.positive()
            .map(|w| (w, true))
            .interleave(self.negative().map(|w| (w, false)))
    }
}

/// Represents a finite sample, which is a pair of positive and negative instances.
#[derive(Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub struct SetSample<A: Alphabet, W: Word<Symbol = A::Symbol> + Hash> {
    pub alphabet: A,
    pub positive: math::Set<W>,
    pub negative: math::Set<W>,
}

/// Type alias for samples over the alphabet `A`, containing finite words which are classified with color `C`,
/// which defaults to `bool`.
pub type FiniteSample<A = CharAlphabet> = SetSample<A, Vec<<A as Alphabet>::Symbol>>;
/// Type alias for samples over alphabet `A` which contain infinite/omega words that are classified with `C`,
/// which defaults to `bool`.
pub type OmegaSample<A = CharAlphabet> = SetSample<A, ReducedOmegaWord<<A as Alphabet>::Symbol>>;

impl<A: Alphabet, W: Word<Symbol = A::Symbol>> SetSample<A, W> {}

impl<A: Alphabet, W: Word<Symbol = A::Symbol>> SetSample<A, W> {
    pub fn count_words(&self) -> usize {
        self.positive.len() + self.negative.len()
    }

    pub fn count_positive_words(&self) -> usize {
        self.positive.len()
    }

    pub fn count_negative_words(&self) -> usize {
        self.negative.len()
    }

    /// Gives an iterator over all positive words in the sample.
    pub fn positive_words(&self) -> impl Iterator<Item = &'_ W> + '_ {
        self.positive.iter()
    }

    /// Gives an iterator over all negative words in the sample.
    pub fn negative_words(&self) -> impl Iterator<Item = &'_ W> + '_ {
        self.negative.iter()
    }

    /// Create a new empty sample for the given alphabet
    pub fn new_for_alphabet(alphabet: A) -> Self {
        Self {
            alphabet,
            positive: math::Set::default(),
            negative: math::Set::default(),
        }
    }

    pub fn into_joined(self, other: Self) -> Self {
        let Self {
            alphabet,
            mut positive,
            mut negative,
        } = self;
        positive.extend(other.positive);
        negative.extend(other.negative);
        Self {
            positive,
            negative,
            alphabet,
        }
    }

    pub fn append(&mut self, other: Self) {
        self.positive.extend(other.positive);
        self.negative.extend(other.negative);
    }

    pub fn as_joined(&self, other: &Self) -> Self
    where
        W: Clone,
    {
        Self {
            alphabet: self.alphabet.clone(),
            positive: self
                .positive
                .iter()
                .chain(other.positive.iter())
                .cloned()
                .collect(),
            negative: self
                .negative
                .iter()
                .chain(other.negative.iter())
                .cloned()
                .collect(),
        }
    }

    /// Returns a reference to the underlying alphabet.
    pub fn alphabet(&self) -> &A {
        &self.alphabet
    }

    /// Gives an iterator over all words in the sample.
    pub fn words(&self) -> impl Iterator<Item = &'_ W> + '_ {
        self.positive.iter().interleave(self.negative.iter())
    }

    /// Returns an iterator over all pairs (w, c) of words w with their classification c that
    /// are present in the sample.
    pub fn entries(&self) -> impl Iterator<Item = (&'_ W, bool)> + '_ {
        self.positive
            .iter()
            .map(|w| (w, true))
            .interleave(self.negative.iter().map(|w| (w, false)))
    }

    /// Classifying a word returns the color that is associated with it.
    pub fn classify<V>(&self, word: &V) -> Option<bool>
    where
        V: Hash + Eq,
        W: Borrow<V>,
    {
        let pos = self.positive.contains(word);
        let neg = self.negative.contains(word);
        assert!(
            !pos || !neg,
            "word cannot be positive and negative at the same time!"
        );
        if pos {
            Some(true)
        } else if neg {
            Some(false)
        } else {
            None
        }
    }

    /// Checks whether a word is contained in the sample.
    pub fn contains(&self, word: &W) -> bool {
        self.positive.contains(word) || self.negative.contains(word)
    }

    /// Inserts given word with given classification. Returns `true` if the word
    /// was not present before.
    pub fn insert(&mut self, word: W, classification: bool) -> bool {
        if classification {
            assert!(!self.negative.contains(&word));
            self.positive.insert(word)
        } else {
            assert!(!self.positive.contains(&word));
            self.negative.insert(word)
        }
    }

    /// Remove the word-value pair equivalent to word and return the classification
    /// if it was part of the sample.
    pub fn remove(&mut self, word: &W) -> Option<bool> {
        if self.positive.swap_remove(word) {
            Some(true)
        } else if self.negative.swap_remove(word) {
            Some(false)
        } else {
            None
        }
    }
}

impl<A, W> Debug for SetSample<A, W>
where
    A: Alphabet + Debug,
    W: Word<Symbol = A::Symbol> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "+ {}\n- {}",
            self.positive_words().map(|x| format!("{x:?}")).join(", "),
            self.negative_words().map(|x| format!("{x:?}")).join(", "),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::passive::SetSample;
    use automata::TransitionSystem;
    use automata::core::alphabet::CharAlphabet;
    use automata::core::upw;
    use automata::core::word::{PeriodicOmegaWord, Word};
    use automata::representation::CollectTs;
    use itertools::Itertools;
    use tracing::info;

    use super::ReducedOmegaWord;

    #[test]
    fn parse_sample() {
        let sample_str = r#"omega
        alphabet: a, b
        positive:
        a
        b,a
        aab
        baa
        negative:
        b
        ab
        abb"#;

        let sample = match SetSample::try_from_str(sample_str) {
            Ok(s) => s,
            Err(e) => panic!("Error parsing sample: {:?}", e),
        };

        assert_eq!(sample.alphabet, CharAlphabet::of_size(2));
        assert_eq!(sample.count_positive_words(), 4);
        assert_eq!(sample.count_negative_words(), 3);
        assert_eq!(sample.classify(&upw!("ab")), Some(false));
    }

    #[test]
    fn to_periodic_sample() {
        let alphabet = CharAlphabet::of_size(2);
        // represents congruence e ~ b ~ aa ~\~ a ~ ab
        let sample = SetSample::new_omega_from_pos_neg(
            alphabet,
            [upw!("ab", "b"), upw!("a", "b"), upw!("bbbbbb")],
            [upw!("aa")],
        );
        let periodic_sample = sample.to_periodic_sample();
        assert_eq!(periodic_sample.positive_size(), 1);
        assert_eq!(periodic_sample.negative_size(), 1);
        assert!(periodic_sample.contains(PeriodicOmegaWord::new("b")));
        assert!(periodic_sample.contains(PeriodicOmegaWord::new("a")));
        assert_eq!(
            periodic_sample.classify(PeriodicOmegaWord::new("bb")),
            Some(true)
        );
    }

    #[test]
    #[ignore]
    fn split_up_sample() {
        let alphabet = CharAlphabet::of_size(2);
        // represents congruence e ~ b ~ aa ~\~ a ~ ab
        let sample = SetSample::new_omega(
            alphabet.clone(),
            vec![
                (upw!("b"), true),
                (upw!("abab"), true),
                (upw!("abbab"), true),
                (upw!("ab"), false),
                (upw!("a"), false),
            ],
        );
        let cong = sample.infer_prefix_congruence().unwrap();
        let split = sample.split(&cong);

        for w in ["b"] {
            assert!(split.get(0).unwrap().contains(&upw!(w)))
        }
    }

    #[test]
    #[ignore]
    fn omega_prefix_tree() {
        let mut w = upw!("aba", "b");
        let x = w.pop_first();

        let words = vec![
            upw!("aba", "b"),
            upw!("a"),
            upw!("ab"),
            upw!("bba"),
            upw!("b", "a"),
            upw!("b"),
            upw!("aa", "b"),
        ];

        let time_start = std::time::Instant::now();
        let cong = crate::prefixtree::prefix_tree(CharAlphabet::from_iter("ab".chars()), words);
        info!(
            "Construction of congruence took {}μs",
            time_start.elapsed().as_micros()
        );

        let dfa = cong.map_state_colors(|_| true).collect_dfa();
        for prf in ["aba", "ababbbbbb", "", "aa", "b", "bbabbab"] {
            assert!(dfa.accepts(prf));
        }
    }
}
