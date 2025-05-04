#![allow(dead_code)]

use crate::core::{
    alphabet::{Alphabet, CharAlphabet, Directional, InvertibleChar},
    math,
};
use crate::ts::{
    Deterministic, DeterministicEdgesFrom, EdgeColor, EdgeExpression, EdgeReference, StateColor,
    StateIndex, SymbolOf,
};
use crate::{Pointed, TransitionSystem};

use super::{Accumulates, RunProfile, TransitionMonoid};

/// Represents the two-sided Cayley graph of a deterministic transition system.
/// In essence, it is a graph using transition profiles of the ts as nodes. It uses
/// a [`Directional`] alphabet to represent concatenation both from the left and the right.
///
/// There are different ways of building the Cayley graph. The most important distinction
/// lies in how two colours are combined, which is determined through the [`Accumulates`] trait.
/// Specifically, the Cayley graph associates a finite word `w` with a transition profile `tp`
/// that describes the behaviour of `w` when applied to/read from any state of the transition system.
///
/// The transformation on the state itself is straightforward as the transition profile can simply
/// store which state is reached. However the encountered edge and state colours need to be taken
/// into account as well. The [`Accumulates`] trait provides a way to combine these colours.
///
/// Since the Cayley graph is merely a way of visualising the transition profiles/transition monoid
/// of a transition system, we defer for an example to [`TransitionMonoid`].
#[derive(Clone)]
pub struct Cayley<Ts: Deterministic<Alphabet = CharAlphabet> + Pointed>
where
    Ts::EdgeColor: Accumulates,
    Ts::StateColor: Accumulates,
{
    alphabet: Directional,
    expressions: math::OrderedMap<SymbolOf<Self>, EdgeExpression<Self>>,
    m: TransitionMonoid<Ts>,
}

/// The right Cayley graph of a deterministic transition system is a graph that uses
/// the transition profiles of the ts as nodes. See [`Cayley`] for more details.
#[derive(Clone)]
pub struct RightCayley<Ts: TransitionSystem + Pointed> {
    expressions: math::OrderedMap<SymbolOf<Ts>, EdgeExpression<Ts>>,
    m: TransitionMonoid<Ts>,
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts> {
        &self.m
    }
}

impl<Ts> TransitionSystem for Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>>;

    type EdgeColor = ();

    type EdgeRef<'this>
        = EdgeReference<'this, InvertibleChar, usize, ()>
    where
        Self: 'this;

    type StateIndices<'this>
        = std::ops::Range<usize>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = Directional;

    fn alphabet(&self) -> &Self::Alphabet {
        &self.alphabet
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.monoid().get_profile(state).map(|p| p.0.clone())
    }
}

impl<Ts> Deterministic for Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Ts::EdgeColor: Accumulates,
    Ts::StateColor: Accumulates,
{
    /// Build a new Cayley graph from the given transition system.
    pub fn new(ts: Ts) -> Self {
        let alphabet = Directional::from_iter(ts.alphabet().universe());
        Self {
            expressions: alphabet.expression_map(),
            m: TransitionMonoid::new(ts),
            alphabet,
        }
    }
}

impl<Ts> Cayley<Ts>
where
    Ts: Deterministic<Alphabet = CharAlphabet> + Pointed,
    Ts::StateColor: Accumulates,
    Ts::EdgeColor: Accumulates,
{
    /// Builds a new Cayley graph from the given transition system and transition monoid.
    pub fn from(ts: Ts, m: TransitionMonoid<Ts>) -> Self {
        let alphabet = Directional::from_iter(ts.alphabet().universe());
        Self {
            expressions: alphabet.expression_map(),
            alphabet,
            m,
        }
    }
}

impl<Ts> RightCayley<Ts>
where
    Ts: TransitionSystem + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Returns a reference to the underlying ts.
    pub fn ts(&self) -> &Ts {
        self.m.ts()
    }

    /// Returns a reference to the [`TransitionMonoid`].
    pub fn monoid(&self) -> &TransitionMonoid<Ts> {
        &self.m
    }
}

impl<Ts> TransitionSystem for RightCayley<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    type StateIndex = usize;

    type StateColor = RunProfile<Ts::StateIndex, StateColor<Ts>, EdgeColor<Ts>>;

    type EdgeColor = ();

    type EdgeRef<'this>
        = EdgeReference<'this, EdgeExpression<Ts>, usize, ()>
    where
        Self: 'this;

    type StateIndices<'this>
        = std::ops::Range<usize>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = DeterministicEdgesFrom<'this, Self>
    where
        Self: 'this;

    type Alphabet = Ts::Alphabet;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts().alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.monoid().profile_indices()
    }
    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(DeterministicEdgesFrom::new(self, state))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.monoid().get_profile(state).map(|p| p.0.clone())
    }
}

impl<Ts> Deterministic for RightCayley<Ts>
where
    Ts: Deterministic + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
}
impl<Ts> RightCayley<Ts>
where
    Ts: TransitionSystem + Pointed,
    StateColor<Ts>: Accumulates,
    EdgeColor<Ts>: Accumulates,
{
    /// Builds a new right Cayley graph from the given transition system and transition monoid.
    pub fn from(ts: Ts, m: TransitionMonoid<Ts>) -> Self {
        Self {
            expressions: ts.alphabet().expression_map(),
            m,
        }
    }
}
