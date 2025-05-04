#![allow(missing_docs)]
use crate::core::{
    Color,
    alphabet::Symbol,
    math,
    word::Infix,
    word::{FiniteWord, OmegaWord, ReducedOmegaWord, Word},
};
use std::{fmt::Debug, marker::PhantomData};

use crate::TransitionSystem;
use crate::ts::{Deterministic, EdgeColor, IndexType, StateColor, StateIndex, SymbolOf};

pub trait Observer<T: TransitionSystem>: Sized {
    type Current;
    fn current(&self) -> &Self::Current;
    fn into_current(self) -> Self::Current;
    fn begin(ts: &T, state: StateIndex<T>) -> Self;
    fn observe_one(
        &mut self,
        ts: &T,
        state: StateIndex<T>,
        sym: SymbolOf<T>,
    ) -> Option<StateIndex<T>>;
}

pub trait InfiniteObserver<T: TransitionSystem>: Observer<T> {
    fn loop_back(seq: &[Self::Current], ts: &T, time: usize) -> Self::Current;
}

#[derive(Debug, Clone, Copy)]
pub struct NoObserver;
#[derive(Debug, Clone, Copy)]
pub struct ReachedState<Idx>(Idx);
#[derive(Debug, Clone)]
pub struct ReachedEdgeColor<T: TransitionSystem>(Option<EdgeColor<T>>);
#[derive(Debug, Clone)]
pub struct ReachedStateColor<T: TransitionSystem>(StateColor<T>);

pub type LeastStateColor<T> = StateColorLimit<T, false>;
pub type GreatestStateColor<T> = StateColorLimit<T, true>;
#[derive(Debug, Clone)]
pub struct StateColorLimit<T: TransitionSystem, const MAX: bool = false>(pub StateColor<T>);

pub type LeastEdgeColor<T> = EdgeColorLimit<T, false>;
pub type GreatestEdgeColor<T> = EdgeColorLimit<T, true>;
#[derive(Debug, Clone)]
pub struct EdgeColorLimit<T: TransitionSystem, const MAX: bool = false>(pub EdgeColor<T>);

#[derive(Clone, Debug)]
pub struct StateSet<T: TransitionSystem>(pub(crate) math::OrderedSet<StateIndex<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateSet<T> {
    type Target = math::OrderedSet<StateIndex<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct StateSequence<T: TransitionSystem>(Vec<StateIndex<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateSequence<T> {
    type Target = Vec<StateIndex<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct StateColorSequence<T: TransitionSystem>(Vec<StateColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateColorSequence<T> {
    type Target = Vec<StateColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct StateColorSet<T: TransitionSystem>(math::Set<StateColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for StateColorSet<T> {
    type Target = math::Set<StateColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
pub struct EdgeColorSet<T: TransitionSystem>(pub(crate) math::Set<EdgeColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for EdgeColorSet<T> {
    type Target = math::Set<EdgeColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug)]
pub struct EdgeColorSequence<T: TransitionSystem>(pub(crate) Vec<EdgeColor<T>>);
impl<T: TransitionSystem> std::ops::Deref for EdgeColorSequence<T> {
    type Target = Vec<EdgeColor<T>>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone)]
pub struct Triggers<T: TransitionSystem>(math::OrderedSet<(StateIndex<T>, SymbolOf<T>)>);
impl<T: TransitionSystem> std::ops::Deref for Triggers<T> {
    type Target = math::OrderedSet<(StateIndex<T>, SymbolOf<T>)>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub struct Run<
    'ts,
    T: Deterministic,
    W: Word<Symbol = SymbolOf<T>>,
    const FINITE: bool,
    O: Observer<T> = NoObserver,
> {
    ts: &'ts T,
    start: StateIndex<T>,
    word: W,
    observer: PhantomData<O>,
}

impl<T: Deterministic, W: Word<Symbol = SymbolOf<T>>, const FINITE: bool, O: Observer<T>> RunResult
    for Run<'_, T, W, FINITE, O>
{
    type StateColor = StateColor<T>;
    type EdgeColor = EdgeColor<T>;
    type StateIndex = StateIndex<T>;
    type Symbol = SymbolOf<T>;
}

impl<'ts, T: Deterministic, W: FiniteWord<Symbol = SymbolOf<T>>, O: Observer<T>>
    Run<'ts, T, W, true, O>
{
    pub fn new_finite(ts: &'ts T, start: StateIndex<T>, word: W) -> Self {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    pub fn evaluate(self) -> FiniteRunOutput<T, W, O> {
        let mut taken = 0;
        let mut observer = O::begin(self.ts, self.start);
        let mut current = self.start;

        while let Some(sym) = self.word.nth(taken) {
            taken += 1;
            if let Some(next) = observer.observe_one(self.ts, current, sym) {
                current = next;
            } else {
                return FiniteRunOutput::Failed(current, EscapePrefix::new(self.word, taken));
            }
        }
        FiniteRunOutput::Reached(current, observer.into_current())
    }
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), FiniteRunOutput::Reached(_, _))
    }
}

impl<'ts, T: Deterministic, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>>
    Run<'ts, T, W, false, O>
{
    pub fn new_infinite(ts: &'ts T, start: StateIndex<T>, word: W) -> Self {
        Run {
            ts,
            start,
            word,
            observer: PhantomData,
        }
    }
    pub fn evaluate(self) -> InfiniteRunOutput<T, W, O> {
        let spoke = self.word.spoke_vec();
        // first evaluate the finite run piece
        let mut current = match self.ts.finite_run_from::<_, O>(self.start, spoke) {
            FiniteRunOutput::Reached(r, _) => r,
            FiniteRunOutput::Failed(state, ep) => {
                return InfiniteRunOutput::Failed(state, ep.with_word(self.word));
            }
        };

        let mut seen = math::OrderedMap::default();
        let mut iteration = 0;
        seen.insert(current, iteration);
        let mut seq = vec![];

        let cycle = self.word.cycle_vec();
        loop {
            iteration += 1;
            match self.ts.finite_run_from::<_, O>(current, &cycle) {
                FiniteRunOutput::Reached(reached, output) => {
                    seq.push(output);
                    if let Some(&prev_iteration) = seen.get(&reached) {
                        return InfiniteRunOutput::Successful(O::loop_back(
                            &seq,
                            self.ts,
                            prev_iteration,
                        ));
                    }
                    seen.insert(reached, iteration);
                    current = reached;
                }
                FiniteRunOutput::Failed(reached, ep) => {
                    let length = self.word.spoke_len()
                        + cycle.len() * (iteration - 1)
                        + ep.shortest_escaping_length;
                    return InfiniteRunOutput::Failed(
                        reached,
                        EscapePrefix {
                            word: self.word,
                            shortest_escaping_length: length,
                        },
                    );
                }
            }
        }
    }
    pub fn is_successful(self) -> bool {
        matches!(self.evaluate(), InfiniteRunOutput::Successful(_))
    }
}

#[derive(Clone)]
pub struct EscapePrefix<W> {
    word: W,
    shortest_escaping_length: usize,
}

impl<W: Word> EscapePrefix<W> {
    pub fn new(word: W, length: usize) -> Self {
        assert!(length > 0);
        Self {
            word,
            shortest_escaping_length: length,
        }
    }
    pub fn as_prefix(&self) -> Infix<'_, W> {
        self.word.prefix(self.shortest_escaping_length)
    }

    pub fn with_word<V>(self, word: V) -> EscapePrefix<V> {
        EscapePrefix {
            word,
            shortest_escaping_length: self.shortest_escaping_length,
        }
    }
    pub fn len(&self) -> usize {
        self.shortest_escaping_length - 1
    }
    pub fn is_empty(&self) -> bool {
        assert!(self.len() > 0);
        false
    }
    pub fn with_length(self, len: usize) -> Self {
        Self {
            word: self.word,
            shortest_escaping_length: len,
        }
    }
    pub fn suffix<S: Symbol>(self) -> ReducedOmegaWord<S>
    where
        W: OmegaWord<Symbol = S>,
    {
        Word::skip(&self.word, self.shortest_escaping_length).reduced()
    }

    pub fn escape_symbol(&self) -> W::Symbol {
        self.word.nth(self.shortest_escaping_length - 1).unwrap()
    }
}

impl<W: Word> Word for EscapePrefix<W> {
    type Symbol = W::Symbol;
    const FINITE: bool = true;
    fn nth(&self, position: usize) -> Option<W::Symbol> {
        if position + 1 >= self.shortest_escaping_length {
            None
        } else {
            self.word.nth(position)
        }
    }
}
impl<W: Word> FiniteWord for EscapePrefix<W> {
    type Symbols<'this>
        = EscapePrefixSymbols<'this, W>
    where
        Self: 'this;
    fn symbols(&self) -> Self::Symbols<'_> {
        EscapePrefixSymbols(self, 0)
    }
}
pub struct EscapePrefixSymbols<'a, W: Word>(&'a EscapePrefix<W>, usize);
impl<W: Word> Iterator for EscapePrefixSymbols<'_, W> {
    type Item = W::Symbol;
    fn next(&mut self) -> Option<Self::Item> {
        if self.1 + 1 >= self.0.shortest_escaping_length {
            None
        } else {
            let out = self.0.nth(self.1).unwrap();
            self.1 += 1;
            Some(out)
        }
    }
}
impl<W: Word> Ord for EscapePrefix<W> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.length_lexicographic_ord(other)
            .then(self.escape_symbol().cmp(&other.escape_symbol()))
    }
}
impl<W: Word> PartialOrd for EscapePrefix<W> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<W: Word> std::hash::Hash for EscapePrefix<W> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.as_prefix().hash(state)
    }
}

impl<W: Word> PartialEq for EscapePrefix<W> {
    fn eq(&self, other: &Self) -> bool {
        self.as_prefix().finite_word_equals(other.as_prefix())
    }
}
impl<W: Word> Eq for EscapePrefix<W> {}
impl<W: Debug> Debug for EscapePrefix<W> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "escape prefix length {} of {:?}",
            self.shortest_escaping_length, self.word
        )
    }
}

pub trait RunResult: Sized {
    /// The type of the state colors.
    type StateColor: Color;
    /// The type of the edge colors.
    type EdgeColor: Color;
    /// The type of the state indices.
    type StateIndex: IndexType;
    /// The type of symbol over which the input word operates.
    type Symbol: Symbol;
    // fn reduced<R:
}

pub enum FiniteRunOutput<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> {
    Reached(StateIndex<T>, O::Current),
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: Word<Symbol = SymbolOf<T>>, O: Observer<T>> FiniteRunOutput<T, W, O> {
    /// Returns the state from which the transition system is left.
    #[allow(unused)]
    fn escape_state(&self) -> Option<StateIndex<T>> {
        match self {
            Self::Reached(_, _) => None,
            Self::Failed(state, _) => Some(*state),
        }
    }
    /// Returns the [`EscapePrefix`] with which the ts is left.
    #[allow(unused)]
    fn escape_prefix(&self) -> Option<&EscapePrefix<W>> {
        match self {
            Self::Reached(_, _) => None,
            Self::Failed(_state, ep) => Some(ep),
        }
    }
    pub fn into_reached_state(self) -> Option<StateIndex<T>> {
        match self {
            Self::Reached(r, _) => Some(r),
            _ => None,
        }
    }
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            Self::Reached(_, o) => Some(o),
            _ => None,
        }
    }
}

pub enum InfiniteRunOutput<
    T: TransitionSystem,
    W: OmegaWord<Symbol = SymbolOf<T>>,
    O: InfiniteObserver<T>,
> {
    Successful(O::Current),
    Failed(StateIndex<T>, EscapePrefix<W>),
}

impl<T: TransitionSystem, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>> Debug
    for InfiniteRunOutput<T, W, O>
where
    W: Debug,
    O::Current: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Failed(q, esc) => {
                write!(f, "failed from {q:?} with escape prefix {esc:?}")
            }
            Self::Successful(ind) => write!(f, "successfully induced {ind:?}"),
        }
    }
}

impl<T: TransitionSystem, W: OmegaWord<Symbol = SymbolOf<T>>, O: InfiniteObserver<T>>
    InfiniteRunOutput<T, W, O>
{
    #[inline(always)]
    pub fn is_successful(&self) -> bool {
        matches!(self, Self::Successful(_))
    }
    #[inline(always)]
    pub fn is_escaping(&self) -> bool {
        !self.is_successful()
    }
    #[inline(always)]
    pub fn into_output(self) -> Option<O::Current> {
        match self {
            Self::Successful(o) => Some(o),
            _ => None,
        }
    }
    #[inline(always)]
    pub fn into_escape_state(self) -> Option<StateIndex<T>> {
        match self {
            Self::Failed(state, _phantom) => Some(state),
            _ => None,
        }
    }
    #[inline(always)]
    pub fn into_escape_prefix(self) -> Option<EscapePrefix<W>> {
        match self {
            Self::Failed(_, ep) => Some(ep),
            _ => None,
        }
    }
}

mod impls {
    use super::*;
    use crate::TransitionSystem;
    use crate::ts::{Deterministic, EdgeColor, IsEdge, StateColor, StateIndex, SymbolOf};
    use automata_core::{Lattice, math};

    impl<T: Deterministic> Observer<T> for NoObserver {
        type Current = ();
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &()
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {}
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            ts.successor_index(state, sym)
        }
    }

    impl<T: Deterministic> InfiniteObserver<T> for NoObserver {
        fn loop_back(_seq: &[Self::Current], _ts: &T, _time: usize) -> Self::Current {}
    }

    impl<T: Deterministic> Observer<T> for ReachedState<StateIndex<T>> {
        type Current = StateIndex<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(state)
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            self.0 = ts.successor_index(state, sym)?;
            Some(self.0)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedStateColor<T> {
        type Current = StateColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap())
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            self.0 = ts.state_color(succ).unwrap();
            Some(succ)
        }
    }
    impl<T: Deterministic> Observer<T> for ReachedEdgeColor<T> {
        type Current = EdgeColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self.0.as_ref().unwrap()
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0.unwrap()
        }
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(None)
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            self.0 = Some(e.color());
            Some(e.target())
        }
    }
    impl<T: Deterministic<StateColor: Lattice>, const MAX: bool> Observer<T>
        for StateColorLimit<T, MAX>
    {
        type Current = StateColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(ts.state_color(state).unwrap())
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let succ = ts.successor_index(state, sym)?;
            if MAX {
                self.0.join_assign(&ts.state_color(succ).unwrap());
            } else {
                self.0.meet_assign(&ts.state_color(succ).unwrap());
            }
            Some(succ)
        }
    }
    impl<T: Deterministic<StateColor: Lattice>, const MAX: bool> InfiniteObserver<T>
        for StateColorLimit<T, MAX>
    where
        StateColor<T>: Default + Ord,
    {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..]
                .iter()
                .min()
                .expect("looping sequence must not be empty")
                .clone()
        }
    }

    impl<T: Deterministic, const MAX: bool> Observer<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Lattice,
    {
        type Current = EdgeColor<T>;
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(if MAX {
                Lattice::bottom()
            } else {
                Lattice::top()
            })
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let e = ts.edge(state, sym)?;
            let new = e.color();
            if MAX {
                self.0.join_assign(&new)
            } else {
                self.0.meet_assign(&new)
            }
            Some(e.target())
        }
    }
    impl<T: Deterministic, const MAX: bool> InfiniteObserver<T> for EdgeColorLimit<T, MAX>
    where
        EdgeColor<T>: Lattice,
    {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            if MAX {
                Lattice::join_iter(seq[time..].iter())
            } else {
                Lattice::meet_iter(seq[time..].iter())
            }
        }
    }

    impl<T: TransitionSystem> Default for StateSet<T> {
        fn default() -> Self {
            Self(Default::default())
        }
    }
    impl<T: Deterministic> Observer<T> for StateSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(math::OrderedSet::from_iter([state]))
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.insert(successor_index);
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(Default::default(), |mut acc, x| {
                acc.0.extend(x.0.iter().cloned());
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for StateSequence<T> {
        type Current = Vec<StateIndex<T>>;
        #[inline(always)]
        fn begin(_ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![state])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.push(successor_index);
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(vec![], |mut acc, x| {
                acc.extend(x);
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for StateColorSequence<T> {
        type Current = Vec<StateColor<T>>;
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            Self(vec![ts.state_color(state).unwrap()])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor_index = ts.successor_index(state, sym)?;
            self.0.push(ts.state_color(successor_index).unwrap());
            Some(successor_index)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateColorSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(vec![], |mut acc, x| {
                acc.extend(x.iter().cloned());
                acc
            })
        }
    }

    impl<T: TransitionSystem> Default for StateColorSet<T> {
        fn default() -> Self {
            Self(Default::default())
        }
    }
    impl<T: Deterministic> Observer<T> for StateColorSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(ts: &T, state: StateIndex<T>) -> Self {
            let start = ts.state_color(state).unwrap();
            Self(math::Set::from_iter([start]))
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.insert(ts.state_color(t.target()).unwrap());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for StateColorSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(Default::default(), |mut acc, x| {
                acc.0.extend(x.0.iter().cloned());
                acc
            })
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSet<T> {
        type Current = Self;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::Set::default())
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            self
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.insert(t.color());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for EdgeColorSet<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            Self(seq[time..].iter().fold(math::Set::default(), |mut acc, x| {
                acc.extend(x.0.iter().cloned());
                acc
            }))
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSet<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for EdgeColorSequence<T> {
        type Current = Vec<EdgeColor<T>>;
        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(vec![])
        }
        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }
        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }
        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let t = ts.edge(state, sym)?;
            self.0.push(t.color());
            Some(t.target())
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for EdgeColorSequence<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            seq[time..].iter().fold(
                Vec::with_capacity((seq.len() - time) * seq[time].len()),
                |mut acc, x| {
                    acc.extend(x.iter().cloned());
                    acc
                },
            )
        }
    }
    impl<T: Deterministic> Clone for EdgeColorSequence<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    impl<T: Deterministic> Observer<T> for Triggers<T> {
        type Current = math::OrderedSet<(StateIndex<T>, SymbolOf<T>)>;

        #[inline(always)]
        fn current(&self) -> &Self::Current {
            &self.0
        }

        #[inline(always)]
        fn into_current(self) -> Self::Current {
            self.0
        }

        #[inline(always)]
        fn begin(_ts: &T, _state: StateIndex<T>) -> Self {
            Self(math::OrderedSet::default())
        }

        #[inline(always)]
        fn observe_one(
            &mut self,
            ts: &T,
            state: StateIndex<T>,
            sym: SymbolOf<T>,
        ) -> Option<StateIndex<T>> {
            let successor = ts.successor_index(state, sym)?;
            self.0.insert((state, sym));
            Some(successor)
        }
    }
    impl<T: Deterministic> InfiniteObserver<T> for Triggers<T> {
        #[inline(always)]
        fn loop_back(seq: &[Self::Current], _ts: &T, time: usize) -> Self::Current {
            assert!(!seq.is_empty());
            assert!(time < seq.len());

            seq[time..]
                .iter()
                .fold(math::OrderedSet::default(), |mut acc, x| {
                    acc.extend(x.iter().cloned());
                    acc
                })
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ts::run::EscapePrefix;
    use crate::ts::{Deterministic, TSBuilder};
    use automata_core::upw;

    #[test]
    fn run_escaping() {
        let dts = TSBuilder::without_colors()
            .with_transitions([(0, 'a', 1), (1, 'a', 0)])
            .into_dts_with_initial(0);

        let w0 = upw!("a");
        assert_eq!(dts.omega_escape_prefix(&w0), None);
        let w1 = upw!("a", "b");
        assert_eq!(
            dts.omega_escape_prefix(&w1),
            Some(EscapePrefix::new(&w1, 2))
        );
    }
}
