mod acceptance_type;
use crate::core::{
    Color,
    alphabet::{Alphabet, CharAlphabet, Matcher},
    word::{FiniteWord, OmegaWord},
};
pub use acceptance_type::OmegaAcceptanceType;

#[macro_use]
mod moore;
pub use moore::{IntoMooreMachine, MooreMachine, MooreSemantics};

#[macro_use]
mod mealy;
pub use mealy::{IntoMealyMachine, MealyLike, MealyMachine, MealySemantics};

mod reachability;
pub use reachability::{DFA, IntoDFA, ReachabilityCondition};

mod omega;
pub use omega::{
    AcceptanceMask, BuchiCondition, DBA, DMA, DPA, DRA, DeterministicOmegaAutomaton, IntoDBA,
    IntoDMA, IntoDPA, IntoDRA, MaxEvenParityCondition, MaxOddParityCondition,
    MinEvenParityCondition, MinOddParityCondition, MullerCondition, NondeterministicOmegaAutomaton,
    OmegaAcceptanceCondition, OmegaAutomaton, RabinCondition, RabinPair,
};

mod with_initial;
use crate::ts::run::{InfiniteObserver, Observer};
pub use with_initial::{WithInitial, WithoutCondition};

/// Defines the semantics of automata, i.e. when something is accepted.
pub mod semantics;
pub use semantics::Semantics;

mod deterministic;

mod priority_mapping;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{
    Deterministic, EdgeExpression, ForAlphabet, IntoEdgeTuple, Shrinkable, Sproutable, StateColor,
    StateIndex, SymbolOf, TSBuilder,
};
use crate::{Congruence, DTS, Pointed, TS, TransitionSystem};
pub use priority_mapping::{StateBasedWeakPriorityMapping, WeakPriorityMapping};

/// Type alias for an omega word automaton, like [`DBA`], [`DMA`], [`DPA`] or [`DRA`].
pub type InfiniteWordAutomaton<A, Z, Q, C, const DET: bool = true, D = TS<A, Q, C, DET>> =
    Automaton<A, Z, Q, C, D, true, DET>;
/// Type alias for a finite word automaton such as a [`DFA`], [`MooreMachine`] or [`MealyMachine`].
pub type FiniteWordAutomaton<A, Z, Q, C, const DET: bool = true, D = TS<A, Q, C, DET>> =
    Automaton<A, Z, Q, C, D, false, DET>;

/// An automaton consists of a transition system and an acceptance condition.
/// There are many different types of automata, which can be instantiated from
/// this struct by setting the type parameters accordingly.
///
/// The const parameter `OMEGA` determines whether the input type of the automaton
/// is finite or omega words. If `OMEGA` is `true`, the automaton accepts omega
/// words, otherwise it accepts finite words.
///
/// The type parameter `D` is the type of the transition system, and `A` is the
/// type of the acceptance condition.
///
/// In order for the automaton to be able to accept words, the acceptance condition
/// must implement the [`Semantics`] trait, depending on the value of `OMEGA` (in the
/// former case `OMEGA` should be false, and in the latter case `OMEGA` should be true).
#[derive(Clone, Eq, PartialEq, Copy)]
pub struct Automaton<
    A: Alphabet,
    Z,
    Q,
    C,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C> = DTS<A, Q, C>,
    const OMEGA: bool = false,
    const DET: bool = true,
> {
    pub(crate) ts: D,
    initial: D::StateIndex,
    acceptance: Z,
}

impl<Z, Q: Color, C: Color + std::hash::Hash + Eq, const OMEGA: bool>
    Automaton<CharAlphabet, Z, Q, C, DTS<CharAlphabet, Q, C>, OMEGA>
{
    /// Instantiates a new [`TSBuilder`] for the edge and state color of `self`.
    pub fn builder() -> TSBuilder<Q, C> {
        TSBuilder::default()
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool, const DET: bool> Automaton<A, Z, Q, C, D, OMEGA, DET>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C>,
{
    /// Creates a new instance of `Self` for the given [`Alphabet`]. Also
    /// takes the colour of the initial state as parameter as this method
    /// simply creates a new transition system and adds a state with the
    /// given color.
    ///
    /// # Example
    /// ```
    /// use automata::{
    ///     automaton::{Automaton, DFA},
    ///     core::alphabet::CharAlphabet,
    ///     ts::{Sproutable, TransitionSystem},
    /// };
    ///
    /// let mut dfa: DFA = Automaton::new_with_initial_color(CharAlphabet::of_size(2), false);
    /// assert_eq!(dfa.size(), 1);
    /// dfa.add_edge((0, 'a', 0));
    /// dfa.add_edge((0, 'b', 0));
    /// assert!(!dfa.accepts("bbabababbabbba"));
    /// ```
    pub fn new_with_initial_color(alphabet: A, initial_color: Q) -> Self
    where
        D: ForAlphabet<A> + Sproutable,
        Z: Default,
    {
        let mut ts = D::for_alphabet(alphabet);
        let initial = ts.add_state(initial_color);
        Self::from_parts(ts, initial)
    }

    /// Uses `Self::new_with_initial_color` to create a new instance of
    /// `Self` and then makes all transitions self-loops emitting the given
    /// color.
    pub fn new_trivial_with_initial_color(alphabet: A, initial_color: Q, edge_color: C) -> Self
    where
        D: ForAlphabet<A> + Sproutable,
        Z: Default,
        C: Clone,
    {
        let alph = alphabet.clone();
        let mut out = Self::new_with_initial_color(alphabet, initial_color);

        let initial = out.initial;
        for sym in alph.universe() {
            out.ts.add_edge((
                initial,
                alph.make_expression(sym),
                edge_color.clone(),
                initial,
            ));
        }
        out
    }

    /// Creates a new automaton from the given transition system and acceptance condition.
    pub fn from_parts_with_acceptance(ts: D, initial: D::StateIndex, acceptance: Z) -> Self {
        Self {
            initial,
            ts,
            acceptance,
        }
    }

    /// Builds a new instance of `Self` from the given parts, that is a transition system `ts` and
    /// a designated `initial` state. Assumes the acceptance type implements `Default`.
    pub fn from_parts(ts: D, initial: D::StateIndex) -> Self
    where
        Z: Default,
    {
        Self::from_parts_with_acceptance(ts, initial, Z::default())
    }

    /// Builds a new instance of `Self` from a given congruence (transition system with designated
    /// initial state) as well as an acceptance condition.
    pub fn from_pointed_with_acceptance(cong: D, acceptance: Z) -> Self
    where
        D: Pointed,
    {
        let initial = cong.initial();
        Self::from_parts_with_acceptance(cong, initial, acceptance)
    }

    /// Builds an instance of `Self` from a pointed transition system. Assumes the acceptance type implements `Default`.
    pub fn from_pointed(cong: D) -> Self
    where
        D: Pointed,
        Z: Default,
    {
        let initial = cong.initial();
        Self::from_parts(cong, initial)
    }

    /// Decomposes the automaton into its parts: the transition system and the acceptance condition.
    pub fn into_parts(self) -> (D, StateIndex<D>, Z) {
        (self.ts, self.initial, self.acceptance)
    }

    /// Returns a reference to the underlying transition system.
    pub fn ts(&self) -> &D {
        &self.ts
    }

    /// Gives a mutable reference to the underlying transition system.
    pub fn ts_mut(&mut self) -> &mut D {
        &mut self.ts
    }

    /// Returns a reference to the acceptance condition.
    pub fn acceptance(&self) -> &Z {
        &self.acceptance
    }
}

impl<A, Z, Q, C, D> Automaton<A, Z, Q, C, D, false, true>
where
    A: Alphabet,
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Z: Semantics<D>,
    Q: Color,
    C: Color,
{
    /// Returns whether the automaton accepts the given finite word.
    pub fn accepts<W: FiniteWord<Symbol = SymbolOf<D>>>(&self, word: W) -> bool
    where
        Z: Semantics<D, false, Output = bool>,
    {
        let Some(output) = self.transform(word) else {
            return false;
        };
        self.acceptance().evaluate(output)
    }

    /// Transforms the given finite word using the automaton, that means it returns
    /// the output of the acceptance condition on the run of the word.
    pub fn transform<W: FiniteWord<Symbol = SymbolOf<D>>>(
        &self,
        word: W,
    ) -> Option<<Z::Observer as Observer<D>>::Current> {
        self.ts
            .finite_run_from::<W, Z::Observer>(self.initial, word)
            .into_output()
    }
}

impl<A, Z, Q, C, D> Automaton<A, Z, Q, C, D, true, true>
where
    A: Alphabet,
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Z: Semantics<D, true>,
    Z::Observer: InfiniteObserver<D>,
    Q: Color,
    C: Color,
{
    /// Returns whether the automaton accepts the given omega word.
    pub fn accepts<W: OmegaWord<Symbol = SymbolOf<D>>>(&self, word: W) -> bool
    where
        Z: Semantics<D, true, Output = bool>,
    {
        let Some(output) = self.transform(word) else {
            return false;
        };
        self.acceptance().evaluate(output)
    }

    /// Transforms the given omega word using the automaton, that means it returns
    /// the output of the acceptance condition on the run of the word.
    pub fn transform<W: OmegaWord<Symbol = SymbolOf<D>>>(
        &self,
        word: W,
    ) -> Option<<Z::Observer as Observer<D>>::Current> {
        self.ts
            .omega_run_from::<W, Z::Observer>(self.initial, word)
            .into_output()
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> AsRef<Self> for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Q: Color,
    C: Color,
{
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> Deterministic for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Q: Color,
    C: Color,
{
}

impl<A, Z, Q, C, D, const OMEGA: bool> PredecessorIterable for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C> + PredecessorIterable,
    Q: Color,
    C: Color,
{
    type PreEdgeRef<'this>
        = D::PreEdgeRef<'this>
    where
        Self: 'this;

    type EdgesToIter<'this>
        = D::EdgesToIter<'this>
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<D>) -> Option<Self::EdgesToIter<'_>> {
        self.ts.predecessors(state)
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> Pointed for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Q: Color,
    C: Color,
{
    fn initial(&self) -> Self::StateIndex {
        self.initial
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> Sproutable for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C> + Sproutable,
    Q: Color,
    C: Color,
{
    fn add_state(&mut self, color: StateColor<Self>) -> Self::StateIndex {
        self.ts.add_state(color)
    }
    fn set_state_color(&mut self, _index: StateIndex<Self>, _color: StateColor<Self>) {
        todo!()
    }
    fn add_edge<E>(&mut self, t: E) -> Option<crate::ts::EdgeTuple<Self>>
    where
        E: IntoEdgeTuple<Self>,
    {
        self.ts.add_edge(t.into_edge_tuple())
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> Shrinkable for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: Shrinkable<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Q: Color,
    C: Color,
{
    fn remove_state(&mut self, q: StateIndex<Self>) -> Option<Self::StateColor> {
        self.ts_mut().remove_state(q)
    }

    fn remove_edges_from_matching(
        &mut self,
        source: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts_mut().remove_edges_from_matching(source, matcher)
    }

    fn remove_edges_between_matching(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts_mut()
            .remove_edges_between_matching(source, target, matcher)
    }
    fn remove_edges_between(
        &mut self,
        source: StateIndex<Self>,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts_mut().remove_edges_between(source, target)
    }

    fn remove_edges_from(
        &mut self,
        source: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts_mut().remove_edges_from(source)
    }

    fn remove_edges_to(
        &mut self,
        target: StateIndex<Self>,
    ) -> Option<Vec<crate::ts::EdgeTuple<Self>>> {
        self.ts_mut().remove_edges_to(target)
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> TransitionSystem for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Q: Color,
    C: Color,
{
    type Alphabet = D::Alphabet;

    type StateIndex = D::StateIndex;

    type StateColor = D::StateColor;

    type EdgeColor = D::EdgeColor;

    type EdgeRef<'this>
        = D::EdgeRef<'this>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = D::EdgesFromIter<'this>
    where
        Self: 'this;

    type StateIndices<'this>
        = D::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.ts.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.ts.state_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        self.ts.edges_from(state)
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.ts.state_color(state)
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool, const DET: bool> std::fmt::Debug
    for Automaton<A, Z, Q, C, D, OMEGA, DET>
where
    A: Alphabet,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = C> + std::fmt::Debug,
    Z: std::fmt::Debug,
    Q: Clone,
    C: Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}\n{:?}", self.acceptance, self.ts)
    }
}

/// Iterator over the accepting states of a [`TransitionSystem`] that have a certain coloring.
pub struct StatesWithColor<'a, Ts: TransitionSystem> {
    ts: &'a Ts,
    iter: Ts::StateIndices<'a>,
    color: Ts::StateColor,
}

impl<'a, Ts: TransitionSystem> StatesWithColor<'a, Ts> {
    /// Creates a new instance for the given transition system and color.
    pub fn new(ts: &'a Ts, color: Ts::StateColor) -> Self {
        Self {
            iter: ts.state_indices(),
            ts,
            color,
        }
    }
}

impl<Ts: TransitionSystem> Clone for StatesWithColor<'_, Ts> {
    fn clone(&self) -> Self {
        Self {
            ts: self.ts,
            iter: self.ts.state_indices(),
            color: self.color.clone(),
        }
    }
}

impl<Ts: TransitionSystem<StateColor = bool>> Iterator for StatesWithColor<'_, Ts> {
    type Item = Ts::StateIndex;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find(|&index| self.ts.state_color(index).unwrap() == self.color)
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> From<D> for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: Congruence<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Z: Default,
    Q: Clone,
    C: Clone,
{
    fn from(value: D) -> Self {
        let initial = value.initial();
        Self::from_parts(value, initial)
    }
}

impl<A, Z, Q, C, D, const OMEGA: bool> From<(D, StateIndex<D>)> for Automaton<A, Z, Q, C, D, OMEGA>
where
    A: Alphabet,
    D: Deterministic<Alphabet = A, StateColor = Q, EdgeColor = C>,
    Z: Default,
    Q: Clone,
    C: Clone,
{
    fn from((ts, initial): (D, StateIndex<D>)) -> Self {
        Self::from_parts(ts, initial)
    }
}

#[cfg(test)]
mod tests {
    use crate::automaton::{DBA, DFA, MooreMachine};
    use crate::representation::CollectTs;
    use automata_core::upw;
    use automata_core::word::ReducedOmegaWord;

    #[test]
    fn mealy_color_or_below() {
        let mm = MooreMachine::builder()
            .with_state_colors([0, 1, 1, 0])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 2),
                (1, 'b', 2),
                (2, 'a', 3),
                (2, 'b', 3),
                (3, 'a', 3),
                (3, 'b', 3),
            ])
            .into_moore(0);

        let dfas = mm.decompose_dfa();
        let dfa1 = &dfas[1];
        let dfa0 = &dfas[0];

        assert!(dfa1.accepts(""));
        assert!(dfa1.accepts("b"));
        assert!(!dfa0.accepts("b"));
        assert!(dfa0.accepts("ba"));
    }

    #[test]
    fn dbas() {
        let dba = DBA::builder()
            .with_edges([
                (0, 'a', true, 1),
                (0, 'b', false, 0),
                (1, 'a', true, 1),
                (1, 'b', false, 0),
            ])
            .into_dba(0);
        assert!(dba.accepts(ReducedOmegaWord::periodic("abb")));
        assert!(!dba.accepts(ReducedOmegaWord::periodic("b")));
        assert!(dba.accepts(upw!("a")));
        assert!(!dba.accepts(upw!("b")));

        assert!(!dba.is_empty());
    }

    #[test]
    fn dfas_and_boolean_operations() {
        let dfa = DFA::builder()
            .with_state_colors([true, false])
            .with_edges([(0, 'a', 1), (0, 'b', 0), (1, 'a', 1), (1, 'b', 0)])
            .into_dfa(0);

        assert!(!dfa.is_empty_language());
        assert_eq!(dfa.give_word(), Some(vec![]));

        let _dfb = dfa.clone();

        assert!(dfa.accepts("ababab"));
        assert!(!dfa.accepts("a"));

        let notdfa = dfa.as_ref().negation().collect_dfa();
        assert!(!notdfa.accepts("ababab"));
        assert!(notdfa.accepts("a"));

        let intersection = dfa.as_ref().intersection(&notdfa).collect_dfa();
        assert!(!intersection.accepts("ababab"));
        assert!(!intersection.accepts("a"));

        let union = dfa.as_ref().union(&notdfa).collect_dfa();
        assert!(union.accepts("ababab"));
        assert!(union.accepts("a"));
    }
}
