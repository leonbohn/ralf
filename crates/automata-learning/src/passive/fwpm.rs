use std::fmt::Debug;

use super::precise::PreciseDPA;
use automata::automaton::MooreMachine;
use automata::core::alphabet::Alphabet;
use automata::core::math;
use automata::ts::StateIndex;
use automata::{RightCongruence, TransitionSystem};
use itertools::Itertools;

/// This structure represents a family of weak priority mappings (FWPM). It consists of a leading
/// congruence ~ and for each class of ~, a mapping that associates finite words with integers.
/// We asssume that these mappings are weak in the sense that for every word `w` and every prefix
/// `u` of `w`, the value assigned to `u` is greater or equal to the one that is assigned to `w`.
#[derive(Clone)]
pub struct FWPM<A: Alphabet> {
    leading: RightCongruence<A>,
    pm: math::OrderedMap<StateIndex<RightCongruence<A>>, MooreMachine<A>>,
}

impl<A: Alphabet> FWPM<A> {
    /// Builds an empty [`FWPM`] with a given leading congruence and no mappings.
    pub fn empty<O: ToOwned<Owned = RightCongruence<A>>>(leading: O) -> Self {
        Self {
            leading: leading.to_owned(),
            pm: math::OrderedMap::default(),
        }
    }

    pub fn complexity(&self) -> usize {
        self.pms()
            .map(|(_, pm)| pm.color_range().len())
            .max()
            .unwrap_or(0)
    }

    /// Returns a reference to the underlying right congruence.
    pub fn leading(&self) -> &RightCongruence<A> {
        &self.leading
    }

    /// Inserts a mapping for some index. If a mapping was already present for this index, it is
    /// wrapped in a `Some` and returned. If no mapping was present, `None` is returned.
    pub fn insert_pm(
        &mut self,
        index: StateIndex<RightCongruence<A>>,
        pm: MooreMachine<A>,
    ) -> Option<MooreMachine<A>> {
        self.pm.insert(index, pm)
    }

    /// Consumes self and builds a [`PreciseDPA`].
    pub fn into_precise_dpa<const N: usize>(self) -> PreciseDPA<A, N> {
        self.into()
    }

    /// Returns an iterator over the progress mealy machines, sorted by the index of the
    /// corresponding congruence class.
    pub fn pms(&self) -> impl Iterator<Item = (StateIndex<RightCongruence<A>>, &MooreMachine<A>)> {
        self.pm
            .iter()
            .sorted_by(|x, y| x.0.cmp(y.0))
            .map(|(i, pm)| (*i, pm))
    }

    /// Constructs a new FWPM from a given right congruence and map associating each class of the congruence
    /// with a priority mapping. Ensures that the each class has a priority mapping.
    pub fn new(
        leading: RightCongruence<A>,
        pm: math::OrderedMap<StateIndex<RightCongruence<A>>, MooreMachine<A>>,
    ) -> Self {
        assert_eq!(
            leading.size(),
            pm.len(),
            "Mismatch in size of congruence and number of priority mappings"
        );
        assert!(
            leading.state_indices().all(|q| pm.contains_key(&q)),
            "Some classes of leading congruence do not have a priority mapping!"
        );
        Self { leading, pm }
    }
}

impl<A: Alphabet> Debug for FWPM<A> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\nleading right congruence\n{:?}", self.leading);
        let names = self.leading.minimal_representatives();
        for (i, prc) in self.pms() {
            write!(
                f,
                "\nprogress right congruence {i} for class {:?}\n{:?}",
                names.get_by_left(&i).unwrap(),
                prc
            )?;
        }
        Ok(())
    }
}
