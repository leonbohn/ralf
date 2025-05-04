use std::fmt::Debug;

use super::fwpm::FWPM;
use automata::automaton::{DFA, DPA};
use automata::core::alphabet::{Alphabet, Matcher};
use automata::core::{Int, Show, Void, math};
use automata::representation::CollectTs;
use automata::ts::{
    Deterministic, EdgeExpression, ForAlphabet, IsEdge, Sproutable, StateColor, StateIndex,
};
use automata::{
    DTS, Pointed, RightCongruence, TransitionSystem,
    dot::{DotStateAttribute, DotTransitionAttribute, Dottable},
};
use itertools::Itertools;
use tracing::{debug, info};

const MAX_PRIORITIES: usize = 8;

pub fn build_precise_dpa_for<A: Alphabet>(fwpm: FWPM<A>) -> DPA<A> {
    match fwpm.complexity() {
        0 => panic!("Precise DPA construction only makes sense if at least one color exists"),
        1 => PreciseDPA::<A, 1>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        2 => PreciseDPA::<A, 2>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        3 => PreciseDPA::<A, 3>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        4 => PreciseDPA::<A, 4>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        5 => PreciseDPA::<A, 5>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        6 => PreciseDPA::<A, 6>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        7 => PreciseDPA::<A, 7>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        8 => PreciseDPA::<A, 8>::from(fwpm)
            .collect_mealy()
            .minimize()
            .collect_dpa(),
        _ => panic!("Too many priorities to construct precise DPA"),
    }
}

type ClassId = u32;
type StateId = u32;

/// We use const generics in the definition of the precise DPA. Therefore, it is necessary to bound the
/// number of colors that can be used. This constant is used as such a bound.
pub const PRECISE_DPA_COLORS: usize = 5;

/// A PState is a state in the precise DPA. It keeps track of the class in the leading
/// congruence and for each Mostowski level, it tracks the class and the state in the
/// corresponding progress DFA. We use const generics (the parameter `N`) to ensure that
/// `PState`s are [`Copy`].
#[derive(Copy, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PState<const N: usize> {
    class: StateIndex,
    progress_classes: [StateIndex; N],
    progress_states: [StateIndex; N],
}

impl<const N: usize> Show for PState<N> {
    fn show(&self) -> String {
        format!(
            "[{}||{}]",
            self.class,
            self.progress_classes()
                .zip(self.progress_states())
                .map(|(c, q)| format!("{c}:{q}"))
                .join(", ")
        )
    }

    fn show_collection<'a, I>(iter: I) -> String
    where
        Self: 'a,
        I: IntoIterator<Item = &'a Self>,
        I::IntoIter: DoubleEndedIterator,
    {
        format!("{{{}}}", iter.into_iter().map(|x| x.show()).join(", "))
    }
}

impl<const N: usize> std::fmt::Display for PState<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{} | {}]",
            self.class,
            self.progress_classes()
                .zip(self.progress_states())
                .map(|(c, q)| format!("({c} - {q})"))
                .join(", ")
        )
    }
}

impl<const N: usize> PState<N> {
    /// Returns the index of the class in the leading congruence.
    pub fn class(&self) -> ClassId {
        self.class
    }

    /// Returns an iterator over the classes of the currently active DFAs.
    pub fn progress_classes(&self) -> impl Iterator<Item = ClassId> + '_ {
        self.progress_classes.iter().cloned()
    }

    /// Returns an iterator over the states of the currently active DFAs.
    pub fn progress_states(&self) -> impl Iterator<Item = StateId> + '_ {
        self.progress_states.iter().cloned()
    }

    /// Creates a new instance of `Self` from the index of the class in the leading
    /// congruence and iterators over the classes and states of the currently active
    /// DFAs.
    pub fn from_iters<I: IntoIterator<Item = ClassId>, J: IntoIterator<Item = StateId>>(
        leading: ClassId,
        pc: I,
        pq: J,
    ) -> Self {
        let mut c = [0; N];
        let mut q = [0; N];
        pc.into_iter().enumerate().for_each(|(i, o)| c[i] = o);
        pq.into_iter().enumerate().for_each(|(i, o)| q[i] = o);
        Self {
            class: leading,
            progress_classes: c,
            progress_states: q,
        }
    }

    /// Creates a new instance of `Self` from the index of the class in the leading
    /// congruence and arrays of the classes and states of the currently active DFAs.
    pub fn new(leading: ClassId, pc: &[ClassId], pq: &[StateId]) -> Self {
        let c = std::array::from_fn(|i| pc[i]);
        let p = std::array::from_fn(|i| pq[i]);

        Self {
            class: leading,
            progress_classes: c,
            progress_states: p,
        }
    }
}

/// The precise DPA is a construction for going from a specifically colored FORC to a deterministic
/// parity automaton. It is described <https://arxiv.org/pdf/2302.11043.pdf>[here, below Lemma 15].
#[derive(Clone)]
pub struct PreciseDPA<A: Alphabet, const N: usize = 8> {
    states: Vec<PState<N>>,
    cong: RightCongruence<A>,
    expressions: math::OrderedMap<A::Symbol, A::Expression>,
    /// Nat -> class -> DFA
    dfas: Vec<[DFA<A>; N]>,
}

/// Represents a transition in a precise DPA.
#[derive(Clone, Copy, Debug)]
pub struct PreciseDPATransition<'a, A: Alphabet, const N: usize> {
    dpa: &'a PreciseDPA<A, N>,
    source: PState<N>,
    expression: &'a A::Expression,
    target: PState<N>,
    color: Int,
}

impl<'a, A: Alphabet, const N: usize> IsEdge<'a, A::Expression, PState<N>, Int>
    for PreciseDPATransition<'a, A, N>
{
    fn source(&self) -> PState<N> {
        self.source
    }
    fn target(&self) -> PState<N> {
        self.target
    }

    fn color(&self) -> Int {
        self.color
    }

    fn expression(&self) -> &'a A::Expression {
        self.expression
    }
}

impl<'a, A: Alphabet, const N: usize> PreciseDPATransition<'a, A, N> {
    /// Creates a new instance of `Self`.
    pub fn new(
        dpa: &'a PreciseDPA<A, N>,
        source: PState<N>,
        expression: &'a A::Expression,
        target: PState<N>,
        color: Int,
    ) -> Self {
        Self {
            dpa,
            source,
            expression,
            target,
            color,
        }
    }
}

/// An iterator over the outgoing edges of a state in a precise DPA.
#[derive(Debug, Clone)]
pub struct PreciseDPAEdgesFrom<'a, A: Alphabet, const N: usize> {
    dpa: &'a PreciseDPA<A, N>,
    expressions: &'a math::OrderedMap<A::Symbol, A::Expression>,
    state: PState<N>,
    it: A::Universe<'a>,
}

impl<'a, A: Alphabet, const N: usize> Iterator for PreciseDPAEdgesFrom<'a, A, N> {
    type Item = PreciseDPATransition<'a, A, N>;

    fn next(&mut self) -> Option<Self::Item> {
        self.it.next().map(|o| {
            let (i, q) = self.dpa.take_precise_transition(&self.state, o);
            PreciseDPATransition::new(
                self.dpa,
                self.state,
                self.expressions
                    .get(&o)
                    .expect("Alphabet expression_map error!"),
                q,
                i,
            )
        })
    }
}

impl<'a, A: Alphabet, const N: usize> PreciseDPAEdgesFrom<'a, A, N> {
    /// Creates a new instance of `Self`.
    pub fn new(dpa: &'a PreciseDPA<A, N>, state: PState<N>) -> Self {
        Self {
            dpa,
            expressions: &dpa.expressions,
            state,
            it: dpa.alphabet().universe(),
        }
    }
}

/// An iterator over the states of a precise DPA.
#[derive(Debug, Clone)]
pub struct PreciseDPAStatesIter<'a, A: Alphabet, const N: usize = 8> {
    dpa: &'a PreciseDPA<A, N>,
    it: std::slice::Iter<'a, PState<N>>,
}

impl<A: Alphabet, const N: usize> TransitionSystem for PreciseDPA<A, N> {
    type StateIndex = PState<N>;

    type StateColor = Void;

    type EdgeColor = Int;

    type EdgeRef<'this>
        = PreciseDPATransition<'this, A, N>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = PreciseDPAEdgesFrom<'this, A, N>
    where
        Self: 'this;
    type StateIndices<'this>
        = automata::ts::Reachable<'this, Self, false>
    where
        Self: 'this;

    type Alphabet = A;

    fn contains_state_index(&self, index: Self::StateIndex) -> bool {
        true
    }

    fn alphabet(&self) -> &Self::Alphabet {
        self.cong.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.reachable_state_indices()
    }
    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        if !self.contains_state_index(state) {
            return None;
        }
        Some(Void)
    }
    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        if !self.contains_state_index(state) {
            return None;
        }
        Some(PreciseDPAEdgesFrom::new(self, state))
    }

    fn maybe_initial_state(&self) -> Option<Self::StateIndex> {
        Some(self.initial())
    }
}

impl<A: Alphabet, const N: usize> Deterministic for PreciseDPA<A, N> {
    fn edge(
        &self,
        state: StateIndex<Self>,
        matcher: impl Matcher<EdgeExpression<Self>>,
    ) -> Option<Self::EdgeRef<'_>> {
        let mut it = self
            .alphabet()
            .universe()
            .filter(|a| matcher.matches(&self.alphabet().make_expression(*a)));
        let symbol = it.next()?;
        assert!(it.next().is_none());

        let (i, p) = self.take_precise_transition(&state, symbol);
        Some(PreciseDPATransition::new(
            self,
            state,
            self.expressions.get(&symbol).unwrap(),
            p,
            i,
        ))
    }
}

impl<A: Alphabet, const N: usize> Pointed for PreciseDPA<A, N> {
    fn initial(&self) -> Self::StateIndex {
        *self.states.first().expect("We add this during creation")
    }
}

impl<A: Alphabet, const N: usize> PreciseDPA<A, N> {
    /// Creates a new precise DPA from the given leading congruence and sequence of sequences of DFAs.
    pub fn new(cong: RightCongruence<A>, dfas: Vec<[DFA<A>; N]>) -> Self {
        let e = cong.initial();
        let initial = PState::from_iters(
            e,
            [e; N],
            (0..dfas.len()).map(|i| dfas[i][e as usize].initial()),
        );
        Self {
            states: vec![initial],
            expressions: cong.alphabet().expression_map(),
            cong,
            dfas,
        }
    }

    pub fn dfas_level(&self, level: usize) -> impl Iterator<Item = (usize, &'_ DFA<A>)> + '_ {
        self.dfas.iter().map(move |dfa| &dfa[level]).enumerate()
    }

    /// Returns a reference to the leading congruence.
    pub fn cong(&self) -> &RightCongruence<A> {
        &self.cong
    }

    /// Given a [`PState`], returns an iterator over the DFAs that are currently active.
    pub fn dfas<'a>(&'a self, q: &'a PState<N>) -> impl Iterator<Item = &'a DFA<A>> + 'a {
        q.progress_classes()
            .enumerate()
            .map(move |(i, c)| &self.dfas[c as usize][i])
    }

    /// Given a [`PState`] and a symbol, returns the index of the least accepting DFA (which is
    /// the priority of the corresponding edge) and the successor [`PState`].
    pub fn take_precise_transition(&self, q: &PState<N>, a: A::Symbol) -> (Int, PState<N>) {
        let d = self
            .cong()
            .successor_index(q.class(), a)
            .expect("Leading congruence must be complete");

        let progress = self
            .dfas(q)
            .zip(q.progress_classes())
            .zip(q.progress_states())
            .map(|((dfa, c), q)| {
                let p = dfa
                    .successor_index(q, a)
                    .expect("all dfas must be complete");
                let b = dfa
                    .state_color(p)
                    .expect("this state must exist as it is successor");
                (c, p, b)
            })
            .collect_vec();

        let least_accepting = progress
            .iter()
            .position(|(_, _, b)| *b)
            .expect("The last DFA must be accepting!");

        let reached_pstate = PState::from_iters(
            d,
            progress
                .iter()
                .enumerate()
                .map(|(i, (c, p, b))| if i < least_accepting { *c } else { d }),
            progress.iter().enumerate().map(|(i, (c, p, b))| {
                if i < least_accepting {
                    *p
                } else {
                    self.dfas[d as usize][i].initial()
                }
            }),
        );

        (
            least_accepting
                .try_into()
                .expect("Should be able to cast to u8"),
            reached_pstate,
        )
    }
}

impl<A: Alphabet, const N: usize> Debug for PreciseDPA<A, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

fn padding_universal_dfa<A: Alphabet>(alphabet: &A) -> DFA<A> {
    let mut dfa = DFA::from_parts(DTS::for_alphabet_size_hint(alphabet.clone(), 1), 0);
    let e = dfa.add_state(true);

    for sym in alphabet.universe() {
        dfa.add_edge((e, alphabet.make_expression(sym), e));
    }
    dfa
}

impl<A: Alphabet, const N: usize> From<FWPM<A>> for PreciseDPA<A, N> {
    fn from(value: FWPM<A>) -> Self {
        let start = std::time::Instant::now();

        let leading = value.leading().clone();
        let padding_dfa = padding_universal_dfa(leading.alphabet());
        let mut prc_dfas = Vec::with_capacity(leading.size());
        for (idx, mm) in value.pms() {
            let mut dfas = mm.decompose_dfa();
            assert!(dfas.len() <= N);
            while dfas.len() < N {
                dfas.push(padding_dfa.clone());
            }
            let array_dfas = dfas
                .try_into()
                .unwrap_or_else(|v| panic!("LENGTH DOES NOT MATCH {N}"));
            prc_dfas.insert(idx as usize, array_dfas);
        }

        debug!(
            "Building precise DPA with {N} priorities took {} microseconds",
            start.elapsed().as_micros()
        );

        Self::new(leading, prc_dfas)
    }
}

impl<A: Alphabet, const N: usize> Dottable for PreciseDPA<A, N> {
    fn dot_name(&self) -> Option<String> {
        Some("PreciseDPA".to_string())
    }

    fn dot_state_ident(&self, idx: Self::StateIndex) -> String {
        format!(
            "p{}{}{}",
            idx.class,
            idx.progress_classes().map(|x| x.to_string()).join(""),
            idx.progress_states().map(|x| x.to_string()).join(""),
        )
    }

    fn dot_state_attributes(
        &self,
        idx: Self::StateIndex,
    ) -> impl IntoIterator<Item = automata::dot::DotStateAttribute>
    where
        (String, StateColor<Self>): Show,
    {
        [
            DotStateAttribute::Shape("box".to_string()),
            DotStateAttribute::Label(idx.to_string()),
        ]
    }

    fn dot_transition_attributes<'a>(
        &'a self,
        t: Self::EdgeRef<'a>,
    ) -> impl IntoIterator<Item = automata::dot::DotTransitionAttribute> {
        [DotTransitionAttribute::Label(format!(
            "{}|{:?}",
            t.expression().show(),
            t.color(),
        ))]
    }
}

#[cfg(test)]
mod tests {
    use automata::core::Void;
    use automata::core::alphabet::CharAlphabet;
    use automata::{DTS, TransitionSystem};

    use super::PreciseDPA;

    #[test]
    fn precise_dpa() {
        let alph = CharAlphabet::of_size(3);

        let cong = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 1),
                (0, 'b', Void, 0),
                (0, 'c', Void, 0),
                (1, 'a', Void, 0),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .default_color(())
            .into_right_congruence_bare(0);

        let de0 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 1),
                (0, 'c', Void, 0),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);
        let da0 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 0),
                (0, 'c', Void, 1),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);

        let de1 = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 0),
                (0, 'b', Void, 2),
                (0, 'c', Void, 1),
                (1, 'a', Void, 0),
                (1, 'b', Void, 2),
                (1, 'c', Void, 2),
                (2, 'a', Void, 2),
                (2, 'b', Void, 2),
                (2, 'c', Void, 2),
            ])
            .with_state_colors([false, false, true])
            .into_dfa(0);

        let full = DTS::builder()
            .with_transitions([
                (0, 'a', Void, 1),
                (0, 'b', Void, 1),
                (0, 'c', Void, 1),
                (1, 'a', Void, 1),
                (1, 'b', Void, 1),
                (1, 'c', Void, 1),
            ])
            .with_state_colors([false, true])
            .into_dfa(0);

        let dfas_e = [de0, de1, full.clone()];
        let dfas_a = [da0, full.clone(), full];

        let dpa = PreciseDPA::new(cong, vec![dfas_e, dfas_a]);
        assert_eq!(dpa.reachable_state_indices().count(), 8);
    }
}
