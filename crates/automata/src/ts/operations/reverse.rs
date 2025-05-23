use crate::TransitionSystem;
use crate::ts::predecessors::PredecessorIterable;
use crate::ts::{IsEdge, StateIndex};

/// Reverses the direction of all transitions in a given [`TransitionSystem`].
#[derive(Clone, Debug)]
pub struct Reversed<Ts>(pub Ts);

impl<'ts, E, Idx, C, T: IsEdge<'ts, E, Idx, C>> IsEdge<'ts, E, Idx, C> for Reversed<T> {
    fn source(&self) -> Idx {
        self.0.target()
    }

    fn target(&self) -> Idx {
        self.0.source()
    }

    fn color(&self) -> C {
        self.0.color()
    }

    fn expression(&self) -> &'ts E {
        self.0.expression()
    }
}

impl<Ts> TransitionSystem for Reversed<Ts>
where
    Ts: PredecessorIterable,
{
    type Alphabet = Ts::Alphabet;

    type StateIndex = Ts::StateIndex;

    type StateColor = Ts::StateColor;

    type EdgeColor = Ts::EdgeColor;

    type EdgeRef<'this>
        = Reversed<Ts::PreEdgeRef<'this>>
    where
        Self: 'this;

    type EdgesFromIter<'this>
        = std::iter::Map<
        Ts::EdgesToIter<'this>,
        fn(Ts::PreEdgeRef<'this>) -> Reversed<Ts::PreEdgeRef<'this>>,
    >
    where
        Self: 'this;

    type StateIndices<'this>
        = Ts::StateIndices<'this>
    where
        Self: 'this;

    fn alphabet(&self) -> &Self::Alphabet {
        self.0.alphabet()
    }

    fn state_indices(&self) -> Self::StateIndices<'_> {
        self.0.state_indices()
    }

    fn edges_from(&self, state: StateIndex<Self>) -> Option<Self::EdgesFromIter<'_>> {
        Some(self.0.predecessors(state)?.map(Reversed))
    }

    fn state_color(&self, state: StateIndex<Self>) -> Option<Self::StateColor> {
        self.0.state_color(state)
    }
}

impl<Ts> PredecessorIterable for Reversed<Ts>
where
    Ts: TransitionSystem + PredecessorIterable,
{
    type PreEdgeRef<'this>
        = Reversed<Ts::EdgeRef<'this>>
    where
        Self: 'this;

    type EdgesToIter<'this>
        = std::iter::Map<
        Ts::EdgesFromIter<'this>,
        fn(Ts::EdgeRef<'this>) -> Reversed<Ts::EdgeRef<'this>>,
    >
    where
        Self: 'this;

    fn predecessors(&self, state: StateIndex<Self>) -> Option<Self::EdgesToIter<'_>> {
        Some(self.0.edges_from(state)?.map(Reversed))
    }
}
