#![allow(missing_docs)]
use std::{collections::VecDeque, fmt::Debug, hash::Hash};

use crate::core::{Show, Void, alphabet::Alphabet, word::FiniteWord};
use crate::ts::{Deterministic, EdgeColor, IndexType, IsEdge, StateColor, SymbolOf};
use crate::{Pointed, TransitionSystem};
use itertools::Itertools;

/// Represents the monoid of transition profiles of a transition system.
///
/// # Examples
/// ```
/// use automata::{
///     core::Void,
///     congruence::{RunProfile, TransitionMonoid},
///     ts::TSBuilder,
/// };
///
/// let dfa = TSBuilder::without_edge_colors()
///     .with_transitions([(0, 'a', 0), (0, 'b', 1), (1, 'a', 1), (1, 'b', 0)])
///     .with_state_colors([false, true])
///     .into_dfa(0);
///
/// let m = TransitionMonoid::new(dfa);
///
/// let bb = m.profile(&"bb");
/// assert_eq!(bb, &RunProfile::new([(0, true, Void), (1, true, Void)]));
/// ```
#[derive(Clone)]
pub struct TransitionMonoid<Ts: TransitionSystem> {
    ts: Ts,
    strings: Vec<(Vec<SymbolOf<Ts>>, ProfileEntry)>,
    #[allow(clippy::type_complexity)]
    tps: Vec<(
        RunProfile<Ts::StateIndex, Ts::StateColor, Ts::EdgeColor>,
        usize,
    )>,
}

/// Encapsulates the behavour of colors along run segments. This is what we are mainly
/// interested in and which we want to keep track of. As an example consider a run segment, where
/// each edge outputs an `usize`. If we are intersted in semantics of a parity automaton,
/// then we mainly want to know what the combined behaviour of the visited edges is.
/// As we use min-parity, this means we take the minimal value along all edges.
pub trait Accumulates: Sized + Clone + Eq + Hash + Ord {
    /// Updates self with the received value.
    fn update(&mut self, other: &Self);
    /// The neutral element with regard to accumulation, which is `false` for booleans and the maximal
    /// `usize::MAX` for integers.
    fn neutral() -> Self;
    /// Accumulate an iterator into a single value.
    fn from_iter<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> Self
    where
        Self: 'a;
    fn from(x: Self) -> Self;
    fn from_or_neutral(x: Option<Self>) -> Self {
        match x {
            Some(x) => Self::from(x),
            None => Self::neutral(),
        }
    }
    fn result(&self) -> &Self;
}

impl Accumulates for bool {
    fn update(&mut self, other: &Self) {
        *self |= *other;
    }

    fn neutral() -> Self {
        false
    }

    fn from_iter<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().any(|x| *x)
    }

    fn from(x: Self) -> Self {
        x
    }

    fn result(&self) -> &Self {
        self
    }
}

impl Accumulates for Void {
    fn update(&mut self, _other: &Self) {}

    fn neutral() -> Self {
        Self
    }

    fn from_iter<'a, I: IntoIterator<Item = &'a Self>>(_iter: I) -> Self
    where
        Self: 'a,
    {
        Self
    }

    fn from(x: Self) -> Self {
        x
    }

    fn result(&self) -> &Self {
        self
    }
}

impl Accumulates for usize {
    fn update(&mut self, other: &Self) {
        *self = std::cmp::min(*self, *other);
    }

    fn neutral() -> Self {
        Self::MAX
    }

    fn from_iter<'a, I: IntoIterator<Item = &'a Self>>(iter: I) -> Self
    where
        Self: 'a,
    {
        iter.into_iter().cloned().min().unwrap_or(Self::MAX)
    }

    fn from(x: Self) -> Self {
        x
    }

    fn result(&self) -> &Self {
        self
    }
}

/// Encapsulates a run piece.
#[derive(Clone, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct RunSignature<Idx, Q, C>(Idx, Q, C);

impl<Idx: IndexType, Q: Accumulates, C: Accumulates> RunSignature<Idx, Q, C> {
    pub fn state(&self) -> Idx {
        self.0
    }

    pub fn sc(&self) -> &Q {
        self.1.result()
    }

    pub fn ec(&self) -> &C {
        self.2.result()
    }
}

impl<Idx: IndexType, Q: Accumulates, C: Accumulates> RunSignature<Idx, Q, C> {
    pub fn empty_from(q: Idx) -> Self {
        Self(q, Q::neutral(), C::neutral())
    }

    pub fn extend_in<Ts>(&self, ts: &Ts, symbol: SymbolOf<Ts>) -> Option<Self>
    where
        Ts: Deterministic<StateIndex = Idx, StateColor = Q, EdgeColor = C>,
    {
        match ts.edge(self.0, symbol) {
            Some(tt) => {
                let target = tt.target();
                let mut sc = Q::from_or_neutral(ts.state_color(target));
                sc.update(self.sc());
                let mut ec = C::from(tt.color().clone());
                ec.update(self.ec());

                Some(Self(target, sc, ec))
            }
            None => None,
        }
    }
    pub fn all_extensions<
        'a,
        Ts: Deterministic<StateIndex = Idx, StateColor = Q, EdgeColor = C>,
    >(
        &'a self,
        ts: &'a Ts,
    ) -> impl Iterator<Item = (SymbolOf<Ts>, Self)> + 'a {
        ts.alphabet()
            .universe()
            .filter_map(|sym| self.extend_in(ts, sym).map(|x| (sym, x)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RunProfile<Idx, Q, C>(Vec<RunSignature<Idx, Q, C>>);

impl<Idx, Q, C> RunProfile<Idx, Q, C> {
    pub fn iter(&self) -> impl Iterator<Item = &'_ RunSignature<Idx, Q, C>> + '_ {
        self.0.iter()
    }
}

impl<Idx: IndexType, Q: Accumulates, C: Accumulates> Show for RunProfile<Idx, Q, C>
where
    Q: Show,
    C: Show,
{
    fn show(&self) -> String {
        let mut out = String::new();
        for (i, rs) in self.0.iter().enumerate() {
            out.push_str(&format!(
                "{i} -{}|{}-> {:?}",
                rs.sc().show(),
                rs.ec().show(),
                rs.state()
            ))
        }
        out
    }
}

impl<Idx: IndexType, Q: Accumulates, C: Accumulates> RunProfile<Idx, Q, C> {
    pub fn new<I: IntoIterator<Item = (Idx, Q, C)>>(iter: I) -> Self {
        Self(
            iter.into_iter()
                .map(|(i, q, c)| RunSignature(i, q, c))
                .collect(),
        )
    }

    pub fn empty<Ts: TransitionSystem<StateIndex = Idx, StateColor = Q, EdgeColor = C>>(
        ts: Ts,
    ) -> Self {
        Self::empty_for_states(ts.state_indices().collect())
    }

    pub fn empty_for_states(states: Vec<Idx>) -> Self {
        Self(
            states
                .into_iter()
                .sorted()
                .map(|q| RunSignature::empty_from(q))
                .collect(),
        )
    }

    pub fn extend_in<Ts>(&self, ts: &Ts, sym: SymbolOf<Ts>) -> Self
    where
        Ts: Deterministic<StateIndex = Idx, StateColor = Q, EdgeColor = C>,
    {
        Self(
            self.0
                .iter()
                .map(|tp| {
                    tp.extend_in(&ts, sym)
                        .expect("we assume the ts to be complete")
                })
                .collect(),
        )
    }

    pub fn all_extensions<
        'a,
        Ts: Deterministic<StateIndex = Idx, StateColor = Q, EdgeColor = C>,
    >(
        &'a self,
        ts: &'a Ts,
    ) -> impl Iterator<Item = (Self, SymbolOf<Ts>)> + 'a {
        ts.alphabet()
            .universe()
            .map(|sym| (self.extend_in(ts, sym), sym))
    }
}

#[derive(Debug, Clone)]
enum ProfileEntry {
    Profile(usize),
    Redirect(usize),
}

impl From<ProfileEntry> for usize {
    fn from(value: ProfileEntry) -> Self {
        match value {
            ProfileEntry::Profile(p) => p,
            ProfileEntry::Redirect(r) => r,
        }
    }
}
impl From<&ProfileEntry> for usize {
    fn from(value: &ProfileEntry) -> Self {
        match value {
            ProfileEntry::Profile(p) => *p,
            ProfileEntry::Redirect(r) => *r,
        }
    }
}

impl<Ts> TransitionMonoid<Ts>
where
    Ts: TransitionSystem,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    pub fn ts(&self) -> &Ts {
        &self.ts
    }

    pub fn elements(&self) -> usize {
        self.tps.len()
    }
}

impl<Ts> TransitionMonoid<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    pub fn new(ts: Ts) -> Self {
        Self::build(ts)
    }
}

impl<Ts> TransitionMonoid<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    #[allow(clippy::type_complexity)]
    pub fn get_profile(
        &self,
        idx: usize,
    ) -> Option<(
        &RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>>,
        &[SymbolOf<Ts>],
    )> {
        let (tp, string_idx) = self.tps.get(idx)?;
        let (word, _) = self.strings.get(*string_idx)?;
        Some((tp, word))
    }

    pub fn get_string(&self, idx: usize) -> Option<(&[SymbolOf<Ts>], usize)> {
        self.strings
            .get(idx)
            .map(|(word, profile)| (word.as_slice(), profile.into()))
    }

    pub fn profile_for<W: FiniteWord<Symbol = SymbolOf<Ts>>>(&self, word: W) -> Option<usize> {
        let (_tp, pe) = self
            .strings
            .iter()
            .find(|(p, _e)| p.finite_word_equals(&word))?;
        match pe {
            ProfileEntry::Profile(p) => Some(*p),
            ProfileEntry::Redirect(r) => Some(*r),
        }
    }

    pub fn profile<W: FiniteWord<Symbol = SymbolOf<Ts>>>(
        &self,
        word: W,
    ) -> &RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>> {
        let idx = self.profile_for(word).expect("Must exist!");
        &self.tps[idx].0
    }

    pub fn profile_indices(&self) -> std::ops::Range<usize> {
        0..self.tps.len()
    }

    fn build(ts: Ts) -> Self {
        let indices = ts.state_indices().collect();
        Self::build_for_states(ts, indices)
    }

    fn build_for_states(ts: Ts, states: Vec<Ts::StateIndex>) -> Self {
        let eps_profile = RunProfile::empty_for_states(states);
        let mut tps = vec![(eps_profile.clone(), 0)];
        let mut strings = vec![(vec![], ProfileEntry::Profile(0))];
        let mut queue = VecDeque::from_iter([(vec![], eps_profile)]);

        while let Some((word, profile)) = queue.pop_front() {
            for (profile_extension, sym) in profile.all_extensions(&ts) {
                assert!(
                    word.len() < ts.size() * 2,
                    "This looks dangerously like an infinite loop..."
                );
                assert!(
                    profile_extension
                        .iter()
                        .all(|tp| ts.contains_state_index(tp.state()))
                );
                let mut word_extension = word.clone();
                word_extension.push(sym);
                if let Some(existing_idx) = tps.iter().position(|(tp, _)| *tp == profile_extension)
                {
                    strings.push((word_extension, ProfileEntry::Redirect(existing_idx)));
                } else {
                    let string_id = strings.len();
                    let profile_id = tps.len();
                    strings.push((word_extension.clone(), ProfileEntry::Profile(profile_id)));
                    tps.push((profile_extension.clone(), string_id));
                    queue.push_back((word_extension, profile_extension));
                    assert!(profile_id < tps.len());
                    assert!(string_id < strings.len());
                }
            }
        }

        Self { ts, tps, strings }
    }
}

impl<Ts> Show for TransitionMonoid<Ts>
where
    Ts: TransitionSystem,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
    for<'b> (&'b Ts::StateColor, &'b Ts::EdgeColor): Show,
{
    fn show(&self) -> String {
        use owo_colors::OwoColorize;
        let mut b = tabled::builder::Builder::default();

        for (word, entry) in &self.strings {
            let mut row = vec![];
            let profile_idx = match entry {
                ProfileEntry::Profile(profile) => {
                    row.push(word.show().bold().to_string());
                    profile
                }
                ProfileEntry::Redirect(redirect) => {
                    row.push(word.show().dimmed().to_string());
                    redirect
                }
            };

            let (profile, _) = self.tps.get(*profile_idx).expect("Must exist!");
            row.extend(
                profile
                    .iter()
                    .map(|tp| format!("{:?}|{}", tp.state(), (tp.sc(), tp.ec()).show().purple(),)),
            );
            b.push_record(row);
        }

        b.build().with(tabled::settings::Style::ascii()).to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::congruence::TransitionMonoid;

    #[test]
    fn tp_from_ts_time() {
        let dfa = crate::ts::TSBuilder::without_edge_colors()
            .with_transitions([(0, 'a', 0), (0, 'b', 1), (1, 'a', 1), (1, 'b', 0)])
            .with_state_colors([false, true])
            .into_dfa(0);

        let start = std::time::Instant::now();
        let tps = TransitionMonoid::build(&dfa);
        tracing::info!(
            "building transition monoid took {} microseconds",
            start.elapsed().as_micros()
        );
        assert_eq!(tps.elements(), 5);
    }
}
