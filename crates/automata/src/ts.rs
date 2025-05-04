use itertools::Itertools;
use tracing::trace;

use crate::core::{
    Color, Show, Void,
    alphabet::{Alphabet, Expression, Matcher},
    math::Partition,
};
use crate::{DTS, congruence::StateNaming};
use std::{collections::BTreeSet, hash::Hash};

mod state_index;
pub use state_index::{IndexType, ScalarIndexType};

mod edge;
pub use edge::{Edge, EdgeReference, IsEdge};

mod transitions_from;
pub use transitions_from::{DeterministicEdgesFrom, TransitionsFrom};

/// Defines implementations for common operations on automata/transition systems.
pub mod operations;

/// This module contains the various provided implementations of [`crate::TransitionSystem`].
pub mod impls;
pub use impls::*;

/// Contains implementations and definitions for dealing with paths through a transition system.
pub mod path;
pub use path::Path;

mod sproutable;
pub use sproutable::{ForAlphabet, IndexedAlphabet, Sproutable};

mod shrinkable;
pub use shrinkable::Shrinkable;

mod deterministic;
pub use deterministic::Deterministic;

mod builder;
pub use builder::TSBuilder;

/// Deals with analysing reachability in transition systems.
pub mod reachable;
pub use reachable::{LengthLexicographicMinimalRepresentatives, Reachable};

/// Contains implementations for SCC decompositions and the corresponding/associated types.
pub mod connected_components;
use connected_components::{SccDecomposition, tarjan_scc_iterative, tarjan_scc_recursive};

/// In this module, everything concering the run of a transition system on a word is defined.
pub mod run;

/// This module defines traits for dealing with predecessors in a transition system.
pub mod predecessors;

mod word_as_ts;
pub use crate::ts::predecessors::PredecessorIterable;
pub use word_as_ts::WordTs;

/// Encapsulates the transition function δ of a (finite) transition system. This is the main trait that
/// is used to query a transition system. Transitions are labeled with a [`Alphabet::Expression`], which
/// determines on which [`Alphabet::Symbol`]s the transition can be taken. Additionally, every transition
/// is labeled with a [`crate::core::Color`], which can be used to store additional information about it, like an
/// associated priority.
///
/// # The difference between transitions and edges
/// Internally, a transition system is represented as a graph, where the states are the nodes and the
/// transitions are the edges. However, the transitions are not the same as the edges.
/// Both store the source and target vertex as well as the color, however an edge is labelled
/// with an expression, while a transition is labelled with an actual symbol (that [`Matcher::matches`]
/// the expression). So a transition is a concrete edge that is taken (usually by the run on a word), while
/// an edge may represent any different number of transitions.
pub trait TransitionSystem: Sized {
    /// The type of the underlying [`Alphabet`].
    type Alphabet: Alphabet;
    /// The type of the indices of the states of the transition system.
    type StateIndex: IndexType;
    /// The type of the colors of the states of the transition system.
    type StateColor: Color;
    /// The type of the colors of the edges of the transition system.
    type EdgeColor: Color;
    /// The type of the references to the transitions of the transition system.
    type EdgeRef<'this>: IsEdge<'this, EdgeExpression<Self>, Self::StateIndex, EdgeColor<Self>>
    where
        Self: 'this;
    /// The type of the iterator over the transitions that start in a given state.
    type EdgesFromIter<'this>: Iterator<Item = Self::EdgeRef<'this>>
    where
        Self: 'this;
    /// Type of the iterator over the state indices.
    type StateIndices<'this>: Iterator<Item = Self::StateIndex>
    where
        Self: 'this;

    /// Returns an iterator over the transitions that start in the given `state`. If the state does
    /// not exist, `None` is returned.
    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>>;

    /// Returns a reference to the alphabet of `self`.
    fn alphabet(&self) -> &Self::Alphabet;

    /// Returns an iterator over the state indices of `self`.
    fn state_indices(&self) -> Self::StateIndices<'_>;

    /// Calls the [`Alphabet::universe`] method on the alphabet of `self`, returning
    /// an iterator of all symbols.
    #[inline(always)]
    fn symbols(&self) -> <Self::Alphabet as Alphabet>::Universe<'_> {
        self.alphabet().universe()
    }

    /// Returns an iterator over the indices of the successors of the given state, if it exists.
    /// Otherwise, the method returns `None`.
    ///
    /// Might produce duplicates.
    fn successor_indices(
        &self,
        state: StateIndex<Self>,
    ) -> Option<impl Iterator<Item = StateIndex<Self>>> {
        Some(self.edges_from(state)?.map(|edge| edge.target()))
    }

    /// Returns a vector of all state indices of `self`. By default, this is simply a helper
    /// calling to [`Self::state_indices`], but it can be overridden to provide a more
    /// efficient implementation.
    #[inline(always)]
    fn state_indices_vec(&self) -> Vec<Self::StateIndex> {
        self.state_indices().collect()
    }

    /// Returns true if the transition system has no states.
    fn is_stateless(&self) -> bool {
        self.state_indices().next().is_none()
    }

    /// Returns an iterator over pairs consisting of a state index and the corresponding state color.
    fn state_indices_with_color(
        &self,
    ) -> impl Iterator<Item = (Self::StateIndex, Self::StateColor)> {
        self.state_indices()
            .map(|q| (q, self.state_color(q).expect("Every state must be colored")))
    }

    /// Helper function which creates an expression from the given symbol.
    /// This is a convenience function that simply calls [`Alphabet::make_expression`].
    fn make_expression(&self, sym: SymbolOf<Self>) -> EdgeExpression<Self> {
        self.alphabet().make_expression(sym)
    }

    /// Gives an iterator over all transitions of `self`.
    fn transitions(&self) -> impl Iterator<Item = Self::EdgeRef<'_>> {
        self.state_indices().flat_map(move |q| {
            self.edges_from(q)
                .expect("should return iterator for state that exists")
        })
    }

    /// Consumes `self` and sets the given `initial` to be the designated initial state. This constructs
    /// an instance of [`crate::automaton::WithInitial`] which is in turn simply an [`crate::Automaton`]
    /// without semantics.
    fn with_initial(self, initial: Self::StateIndex) -> crate::automaton::WithInitial<Self>
    where
        Self: Sized,
    {
        crate::automaton::WithInitial::from_parts(self, initial)
    }

    /// Returns true if the transition system has no edges. This is rather costly, as it
    /// simply iterates over all states and checks whether they have any outgoing edges.
    /// Should be overridden if a more efficient implementation is available.
    fn is_edgeless(&self) -> bool {
        self.state_indices().all(|q| {
            self.edges_from(q)
                .map(|mut it| it.next().is_none())
                .unwrap_or(true)
        })
    }

    /// Returns an iterator giving all colors that are used by the edges of `self`.
    /// Note that this **may output the same color multiple times**, if it is used by multiple
    /// edges. If that is not desired, use [`Self::edge_colors_unique()`] instead.
    ///
    /// A call is rather costly, as it simply iterates over all states and collects the
    /// colors of the outgoing edges. Should be overridden if a more efficient implementation
    /// is available.
    fn edge_colors(&self) -> impl Iterator<Item = Self::EdgeColor>
    where
        EdgeColor<Self>: Clone,
    {
        self.state_indices()
            .flat_map(|q| {
                self.edges_from(q)
                    .expect("should return iterator for state that exists")
            })
            .map(|t| t.color().clone())
    }

    /// Returns an iterator giving all **unique** colors that are used by the edges of `self`.
    /// By default, a call is rather costly as it simply iterates over all states and collects
    /// the colors of the outgoing edges. Should be overridden if a more efficient implementation
    /// is available.
    fn edge_colors_unique(&self) -> impl Iterator<Item = Self::EdgeColor>
    where
        EdgeColor<Self>: Eq + Hash + Clone,
    {
        self.edge_colors().unique()
    }

    /// Returns an iterator over all transitions that start in the given `state` and whose expression
    /// matches the given `sym`. If the state does not exist, `None` is returned.
    fn edges_matching(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<impl Iterator<Item = EdgeRef<'_, Self>>>
    where
        EdgeColor<Self>: Clone,
    {
        Some(
            self.edges_from(state)?
                .filter(move |t| matcher.matches(t.expression())),
        )
    }

    /// Returns true if the transition system is deterministic, i.e. if there are no two edges leaving
    /// the same state with the same symbol.
    fn is_deterministic(&self) -> bool {
        for state in self.state_indices() {
            for (l, r) in self
                .edges_from(state)
                .unwrap()
                .zip(self.edges_from(state).unwrap().skip(1))
            {
                if self.alphabet().overlapping(l.expression(), r.expression()) {
                    trace!(
                        "found overlapping edges from {:?}: on {} to {:?} and on {} to {:?}",
                        l.source(),
                        l.expression().show(),
                        l.target(),
                        r.expression().show(),
                        r.target(),
                    );
                    return false;
                }
            }
        }
        true
    }

    /// Checks whether `self` is complete, meaning every state has a transition for every symbol
    /// of the alphabet.
    fn is_complete(&self) -> bool {
        let universe = self.alphabet().universe().collect::<BTreeSet<_>>();

        for q in self.state_indices() {
            let syms = self
                .transitions_from(q)
                .map(|(_q, a, _c, _p)| a)
                .collect::<BTreeSet<_>>();

            assert!(
                syms.is_subset(&universe),
                "Makes no sense to have more symbols on transitions than in the alphabet"
            );
            if !universe.is_subset(&syms) {
                return false;
            }
        }
        true
    }

    /// Returns true if and only if there exists a transition from the given `source` state to the
    /// given `target` state, whose expression is matched by the given `sym`. If either the source
    /// or the target state does not exist, `false` is returned.
    fn has_transition(
        &self,
        source: StateIndex<Self>,
        sym: SymbolOf<Self>,
        target: StateIndex<Self>,
    ) -> bool {
        if let Some(mut it) = self.edges_from(source) {
            it.any(|t| t.target() == target && t.expression().matched_by(sym))
        } else {
            false
        }
    }

    /// Returns an iterator over the transitions that start in the given `state`. Panics if the
    /// state does not exist.
    fn transitions_from(&self, state: StateIndex<Self>) -> TransitionsFrom<'_, Self> {
        TransitionsFrom::new(self, state)
    }

    /// Commence a new subset construction starting from the collection of states given by `states`.
    /// This is a convenience function that simply calls [`operations::SubsetConstruction::new`]. It produces a
    /// deterministic transition system operating on sets of states.
    fn subset_construction_from<I: IntoIterator<Item = Self::StateIndex>>(
        self,
        states: I,
    ) -> operations::SubsetConstruction<Self> {
        operations::SubsetConstruction::new(self, states)
    }

    /// Performs a subset construction using [`Self::subset_construction_from`] starting with a singleton
    /// set containing the only initial state of `self`.
    fn subset_construction(self) -> operations::SubsetConstruction<Self>
    where
        Self: Pointed,
    {
        let initial = self.initial();
        operations::SubsetConstruction::new_from(self, initial)
    }

    /// Returns the color of the given `state`, if it exists. Otherwise, `None` is returned.
    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor>;

    /// Attempts to find a word which leads from the state `from` to state `to`. If no such
    /// word exists, `None` is returned.
    fn word_from_to(
        &self,
        from: StateIndex<Self>,
        to: StateIndex<Self>,
    ) -> Option<Vec<SymbolOf<Self>>>
    where
        Self: Sized,
    {
        self.minimal_representatives_iter_from(from)
            .find_map(|rep| {
                if rep.state_index() == to {
                    Some(rep.decompose().0)
                } else {
                    None
                }
            })
    }

    /// Gives the size of `self`, which is obtained simply by counting the number of elements yielded by [`Self::state_indices()`].
    fn size(&self) -> usize {
        self.state_indices().count()
    }

    /// Gives a hint for the size of `self`. The first element is the minimum number of states that
    /// are in the transition system. The second element is the maximum number of states that are in
    /// the transition system. If the maximum number is not known, `None` is returned.
    fn hint_size(&self) -> (usize, Option<usize>) {
        (0, None)
    }

    /// Returns `true` if and only if there exists at least one state.
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Returns true if and only if the given state `index` exists.
    #[inline(always)]
    fn contains_state_index(&self, index: Self::StateIndex) -> bool {
        self.state_indices().contains(&index)
    }

    /// Tries to find the index of a state with the given `color`. Note that this uses `find` and thus
    /// returns the first such state that is found. There is no guarantee on the order in which the states
    /// are visited such that if more than one state with the given `color` exists, subsequent calls to
    /// this method may return different indices.
    #[inline(always)]
    fn find_by_color(&self, color: &StateColor<Self>) -> Option<Self::StateIndex>
    where
        StateColor<Self>: Eq,
    {
        self.state_indices()
            .find(|index| self.state_color(*index).as_ref() == Some(color))
    }

    /// Returns true if and only if a state with the given `color` exists.
    #[inline(always)]
    fn contains_state_color(&self, color: &StateColor<Self>) -> bool
    where
        StateColor<Self>: Eq,
    {
        self.find_by_color(color).is_some()
    }

    /// Builds the [`operations::Quotient`] of `self` with regard to some given [`Partition`].
    #[inline(always)]
    fn quotient(self, partition: Partition<Self::StateIndex>) -> operations::Quotient<Self>
    where
        Self: Sized,
    {
        operations::Quotient::new(self, partition)
    }

    /// Restricts the edges of `self` such that only transitions p --a|c--> q exist where
    /// `min` <= `c` <= `max`, i.e. all transitions where either `c` < `min` or `max` < `c`
    /// are discarded.
    #[inline(always)]
    fn edge_color_restricted(
        self,
        min: Self::EdgeColor,
        max: Self::EdgeColor,
    ) -> operations::EdgeColorRestricted<Self> {
        operations::EdgeColorRestricted::new(self, min, max)
    }

    /// Restricts the state indices with the given function. This means that only the states for
    /// which the function returns `true` are kept, while all others are removed.
    #[inline(always)]
    fn restrict_state_indices<F>(self, filter: F) -> operations::RestrictByStateIndex<Self, F>
    where
        Self: Sized,
        F: operations::StateIndexFilter<Self::StateIndex>,
    {
        operations::RestrictByStateIndex::new(self, filter)
    }

    /// Recolors the edges of `self` with the given function `f`. This works akin to
    /// [`Self::map_edge_colors()`] but allows for a more fine-grained control over the
    /// recoloring process, by giving access not only to the color itself, but also to
    /// the origin, target and expression of the respective edge.
    #[inline(always)]
    fn map_edge_colors_full<D, F>(self, f: F) -> operations::MapEdges<Self, F>
    where
        F: Fn(Self::StateIndex, &EdgeExpression<Self>, Self::EdgeColor, Self::StateIndex) -> D,
        D: Clone,
        Self: Sized,
    {
        operations::MapEdges::new(self, f)
    }

    /// Removes all coloring from `self`, giving a transition system that has edges and states
    /// colored with type [`Void`].
    #[inline(always)]
    fn erase_colors(self) -> operations::EraseColors<Self>
    where
        Self: Sized,
    {
        self.erase_state_colors().erase_edge_colors()
    }

    /// Completely removes the edge coloring.
    #[inline(always)]
    fn erase_edge_colors(self) -> operations::MapEdgeColor<Self, fn(Self::EdgeColor) -> Void>
    where
        Self: Sized,
    {
        self.map_edge_colors(|_| Void)
    }

    /// Completely removes the state coloring.
    #[inline(always)]
    fn erase_state_colors(self) -> operations::MapStateColor<Self, fn(Self::StateColor) -> Void>
    where
        Self: Sized,
    {
        self.map_state_colors(|_| Void)
    }

    /// Map the edge colors of `self` with the given function `f`.
    #[inline(always)]
    fn map_edge_colors<D: Clone, F: Fn(Self::EdgeColor) -> D>(
        self,
        f: F,
    ) -> operations::MapEdgeColor<Self, F>
    where
        Self: Sized,
    {
        operations::MapEdgeColor::new(self, f)
    }

    /// Consumes and recolors `self` with the colors as given by `provider`.
    /// See more possible ways of assigning colors in [`operations::ProvidesStateColor`].
    ///
    /// # Example
    /// ```
    /// use automata::ts::{TSBuilder, Deterministic, operations::UniformColor, TransitionSystem};
    ///
    /// let ts = TSBuilder::without_colors()
    ///     .with_edges([(0, 'a', 1), (1, 'a', 2), (2, 'a', 0)])
    ///     .into_dts_with_initial(0);
    /// let colored = ts.with_state_color(UniformColor(false));
    /// assert_eq!(colored.reached_state_color("a"), Some(false));
    /// assert_eq!(colored.with_state_color(UniformColor(true)).reached_state_color("a"), Some(true));
    /// ```
    #[inline(always)]
    fn with_state_color<P: ProvidesStateColor<Self::StateIndex>>(
        self,
        provider: P,
    ) -> WithStateColor<Self, P> {
        WithStateColor::new(self, provider)
    }

    /// Map the state colors of `self` with the given function.
    #[inline(always)]
    fn map_state_colors<D: Clone, F: Fn(Self::StateColor) -> D>(
        self,
        f: F,
    ) -> operations::MapStateColor<Self, F>
    where
        Self: Sized,
    {
        operations::MapStateColor::new(self, f)
    }

    /// Turns `self` into a DFA that accepts all words, i.e. all states are accepting.
    fn all_accepting_dfa(self) -> operations::MapStateColor<Self, fn(Self::StateColor) -> bool>
    where
        Self: Sized,
    {
        self.map_state_colors(|_| true)
    }

    /// Computes the [`connected_components::SccDecomposition`] of self, restricted
    /// to the set of vertices that is given.
    #[inline(always)]
    fn reachable_sccs_from<I: IntoIterator<Item = StateIndex<Self>>>(
        &self,
        from: I,
    ) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        connected_components::tarjan_scc_iterative_from(self, from)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    #[inline(always)]
    fn sccs(&self) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_iterative(self)
    }

    /// Performs an SCC decomposition of self using Kosaraju's algorithm, starting from the state `start`. This is an
    /// efficient algorithm and it might provide more performance over Tarjan's algorithm in some cases.
    fn sccs_kosaraju(&self, start: Self::StateIndex) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
        Self: PredecessorIterable,
    {
        connected_components::kosaraju(self, start)
    }

    /// Obtains the [`connected_components::SccDecomposition`] of self, which is a partition of the states into strongly
    /// connected components. Uses Tarjan's algorithm.
    fn sccs_recursive(&self) -> SccDecomposition<'_, Self>
    where
        Self: Sized,
    {
        tarjan_scc_recursive(self)
    }

    /// Returns `true` iff the given state is reachable from the initial state.
    fn is_reachable(&self, state: StateIndex<Self>) -> bool
    where
        Self: Sized + Pointed,
    {
        self.is_reachable_from(self.initial(), state)
    }

    /// Returns `true` iff the given `state` is reachable from the given `origin` state.
    fn is_reachable_from(&self, origin: StateIndex<Self>, state: StateIndex<Self>) -> bool
    where
        Self: Sized,
    {
        assert!(self.contains_state_index(origin));
        assert!(self.contains_state_index(state));
        self.reachable_state_indices_from(origin)
            .any(|s| s == state)
    }

    /// Gives a canonical state naming for the states of `self`, based
    /// on the minimal repesentatives of the states.
    fn canonical_naming(&self) -> StateNaming<Self>
    where
        Self: Sized + Pointed,
    {
        self.canonical_naming_from(self.initial())
    }

    /// Gives a canonical state naming for the states of `self` with
    /// respect to the given starting state. See [`Self::canonical_naming`].
    fn canonical_naming_from(&self, origin: StateIndex<Self>) -> StateNaming<Self>
    where
        Self: Sized + Pointed,
    {
        StateNaming::from_iter(self.minimal_representatives_iter_from(origin))
    }

    /// Returns an iterator over the minimal representative (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the initial state.
    fn minimal_representatives_iter(&self) -> LengthLexicographicMinimalRepresentatives<'_, Self>
    where
        Self: Sized + Pointed,
    {
        LengthLexicographicMinimalRepresentatives::new(self, self.initial())
    }

    /// Returns an iterator over the minimal representatives (i.e. length-lexicographically minimal
    /// word reaching the state) of each state that is reachable from the given `state`.
    fn minimal_representatives_iter_from(
        &self,
        state: StateIndex<Self>,
    ) -> LengthLexicographicMinimalRepresentatives<'_, Self> {
        LengthLexicographicMinimalRepresentatives::new(self, state)
    }

    /// Returns an iterator over the indices of the states that are reachable from the initial state. The iterator yields tuples
    /// (State Index, State Color)
    fn reachable_states(&self) -> Reachable<'_, Self, false>
    where
        Self: Sized + Pointed,
    {
        Reachable::new(self, self.initial())
    }

    /// Returns an iterator over all state colors that are reachable from the initial state. May yield the same color multiple times.
    fn reachable_state_colors(&self) -> impl Iterator<Item = Self::StateColor> + '_
    where
        Self: Sized + Pointed,
    {
        self.reachable_states()
            .map(|q| self.state_color(q).unwrap())
    }

    /// Returns an iterator over the indices of the states that are reachable from the initial state.
    fn reachable_state_indices(&self) -> Reachable<'_, Self, false>
    where
        Self: Sized + Pointed,
    {
        self.reachable_state_indices_from(self.initial())
    }

    /// Returns an iterator over the indices of the states that are reachable from the given `state`.
    fn reachable_state_indices_from(&self, state: Self::StateIndex) -> Reachable<'_, Self, false>
    where
        Self: Sized,
    {
        Reachable::state_indices(self, state)
    }

    /// Returns an iterator over the states that are reachable from the given `state`.
    fn reachable_states_from(&self, state: StateIndex<Self>) -> Reachable<'_, Self>
    where
        Self: Sized,
    {
        Reachable::new(self, state)
    }

    /// Returns an option containing the index of the initial state, if it exists.
    /// This is a somewhat hacky way of dealing with the fact that we cannot express
    /// negative trait bounds. In particular, we cannot express that a transition system
    /// is not pointed, which prevents us from correctly implementing e.g. the `ToDot`
    /// trait for non-pointed transition systems. This function is a workaround for this
    /// problem, as it allows us to check whether a transition system is pointed or not,
    /// since the provided default implementation assumes that the no initial state exists.
    fn maybe_initial_state(&self) -> Option<Self::StateIndex> {
        None
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this>
        = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this>
        = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        Ts::state_indices(self)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        Ts::state_color(self, state)
    }
}

impl<Ts: TransitionSystem> TransitionSystem for &mut Ts {
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this>
        = Ts::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = Ts::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this>
        = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        Ts::alphabet(self)
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        Ts::state_indices(self)
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Ts::edges_from(self, state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        Ts::state_color(self, state)
    }
}

/// Implementors of this trait can be transformed into a owned tuple representation of
/// an edge in a [`TransitionSystem`].
pub trait IntoEdgeTuple<Ts: TransitionSystem> {
    /// Consumes `self` and returns a tuple representing an edge in a [`TransitionSystem`].
    /// Owned edges in their tuple representation may simply be cloned, whereas if we have
    /// a tuple represetation of an edge with a borrowed expression, this operation may
    /// have to clone the expression.
    fn into_edge_tuple(self) -> EdgeTuple<Ts>;
}

impl<T: TransitionSystem> IntoEdgeTuple<T> for EdgeTuple<T> {
    #[inline(always)]
    fn into_edge_tuple(self) -> Self {
        self
    }
}

impl<T: TransitionSystem<EdgeColor = Void>> IntoEdgeTuple<T>
    for (StateIndex<T>, EdgeExpression<T>, StateIndex<T>)
{
    #[inline(always)]
    fn into_edge_tuple(self) -> EdgeTuple<T> {
        (self.0, self.1, Void, self.2)
    }
}

impl<T: TransitionSystem, TT: IntoEdgeTuple<T>> IntoEdgeTuple<T> for &TT
where
    TT: Clone,
{
    #[inline(always)]
    fn into_edge_tuple(self) -> EdgeTuple<T> {
        self.clone().into_edge_tuple()
    }
}

/// Helper trait for extracting the [`crate::core::alphabet::Symbol`] type from an a transition system.
pub type SymbolOf<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Symbol;
/// Helper trait for extracting the [`crate::core::alphabet::Expression`] type from an a transition system.
pub type EdgeExpression<A> = <<A as TransitionSystem>::Alphabet as Alphabet>::Expression;
/// Type alias for extracting the state color in a [`TransitionSystem`].
pub type StateColor<X> = <X as TransitionSystem>::StateColor;
/// Type alias for extracting the edge color in a [`TransitionSystem`].
pub type EdgeColor<X> = <X as TransitionSystem>::EdgeColor;
/// Type alias for extracting the state index in a [`TransitionSystem`].
pub type StateIndex<X = DTS> = <X as TransitionSystem>::StateIndex;
/// Type alias for a tuple representing an edge in a [`TransitionSystem`].
pub type EdgeTuple<Ts> = (
    StateIndex<Ts>,
    EdgeExpression<Ts>,
    EdgeColor<Ts>,
    StateIndex<Ts>,
);
/// Type alias to obtain the type of a reference to an edge in a given [`TransitionSystem`].
pub type EdgeRef<'a, T> = <T as TransitionSystem>::EdgeRef<'a>;

/// Implementors of this trait have a distinguished (initial) state.
pub trait Pointed: TransitionSystem {
    /// Returns the index of the initial state.
    fn initial(&self) -> Self::StateIndex;

    /// Returns the color of the initial state.
    fn initial_color(&self) -> Self::StateColor {
        self.state_color(self.initial())
            .expect("Initial state must exist and be colored!")
    }
}

impl<P: Pointed> Pointed for &P {
    fn initial(&self) -> Self::StateIndex {
        P::initial(self)
    }
}

impl<P: Pointed> Pointed for &mut P {
    fn initial(&self) -> Self::StateIndex {
        P::initial(self)
    }
}

use self::operations::{ProvidesStateColor, WithStateColor};

#[cfg(test)]
mod tests {}
