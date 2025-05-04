use std::{io::BufRead, ops::Deref};

use crate::automaton::{
    AcceptanceMask, DeterministicOmegaAutomaton, OmegaAcceptanceCondition, OmegaAutomaton,
};
use crate::core::{
    Int,
    alphabet::{PropAlphabet, PropExpression},
};
use crate::ts::{ForAlphabet, Sproutable, TransitionSystem};
use hoars::HoaRepresentation;
use tracing::{trace, warn};

use super::HoaString;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IntoDeterministicHoaAutomatonStream<R> {
    base: HoaAutomatonStream<R, false>,
}

impl<R> IntoDeterministicHoaAutomatonStream<R> {
    pub fn new(read: R) -> Self {
        Self {
            base: HoaAutomatonStream::new(read),
        }
    }
}

impl<R: BufRead> Iterator for IntoDeterministicHoaAutomatonStream<R> {
    type Item = DeterministicOmegaAutomaton<PropAlphabet>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.base.next() {
                None => return None,
                Some(aut) => {
                    if let Ok(det) = aut.try_into_deterministic() {
                        return Some(det);
                    } else {
                        warn!("Encountered automaton that is not deterministic, skipping...")
                    }
                }
            }
        }
    }
}

pub type NoneterministicHoaAutomatonStream<R> = HoaAutomatonStream<R, false>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaAutomatonStream<R, const DET: bool = true> {
    read: R,
    buf: String,
    pos: usize,
}

impl<R: BufRead, const DET: bool> Iterator for HoaAutomatonStream<R, DET> {
    type Item = OmegaAutomaton<PropAlphabet, DET>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.read.read_line(&mut self.buf) {
                Ok(0) => return None,
                Ok(read_bytes) => {
                    if self.buf[self.pos..].contains("--ABORT--") {
                        trace!("encountered --ABORT-- in stream, resetting");
                        self.buf.clear();
                        self.pos = 0;
                        continue;
                    }

                    if self.buf[self.pos..].contains("--END--") {
                        let end = self.pos + "--END--".len();
                        trace!(
                            "encountered --END-- in stream, attempting to parse automaton \n{}",
                            &self.buf[..end]
                        );
                        let aut: Result<OmegaAutomaton<PropAlphabet, DET>, _> =
                            parse_omega_automaton_range(&self.buf, 0, end);
                        self.buf.clear();
                        self.pos = 0;

                        match aut {
                            Err(e) => {
                                warn!(
                                    "Encountered automaton that could not be parsed, skipping... {:?}",
                                    e
                                );
                            }
                            Ok(aut) => {
                                assert!(!DET || aut.ts().is_deterministic(), "type error");
                                return Some(aut);
                            }
                        }
                    }

                    self.pos += read_bytes;
                }
                Err(_e) => return None,
            }
        }
    }
}

impl<R, const DET: bool> HoaAutomatonStream<R, DET> {
    pub fn new(read: R) -> Self {
        Self {
            read,
            pos: 0,
            buf: String::new(),
        }
    }
}

pub fn parse_omega_automaton_range<const DET: bool>(
    hoa: &str,
    start: usize,
    end: usize,
) -> Result<OmegaAutomaton<PropAlphabet, DET>, String> {
    match HoaRepresentation::try_from(&hoa[start..end]) {
        Ok(aut) => match OmegaAutomaton::try_from(aut) {
            Ok(aut) => Ok(aut),
            Err(e) => Err(format!(
                "In range {}..{}, could not convert automaton into omega automaton: {}",
                start, end, e
            )),
        },
        Err(e) => Err(format!(
            "Could not parse automaton from range {}..{}: {}",
            start, end, e
        )),
    }
}

pub fn pop_deterministic_omega_automaton(
    hoa: HoaString,
) -> Option<(DeterministicOmegaAutomaton<PropAlphabet>, HoaString)> {
    pop_omega_automaton(hoa)
}

/// Tries to `pop` the foremost valid HOA automaton from the given [`HoaString`].
/// If no valid automaton is found before the end of the stream is reached, the
/// function returns `None`.
pub fn pop_omega_automaton<const DET: bool>(
    hoa: HoaString,
) -> Option<(OmegaAutomaton<PropAlphabet, DET>, HoaString)> {
    let mut hoa = hoa;
    const END_LEN: usize = "--END--".len();
    const ABORT_LEN: usize = "--ABORT--".len();

    loop {
        match (hoa.0.find("--ABORT--"), hoa.0.find("--END--")) {
            (None, Some(pos)) => {
                trace!("Returnting first automaton, going up to position {pos}");
                match parse_omega_automaton_range(&hoa.0, 0, pos + END_LEN) {
                    Ok(aut) => {
                        return Some((
                            aut,
                            HoaString(hoa.0[pos + END_LEN..].trim_start().to_string()),
                        ));
                    }
                    Err(e) => {
                        warn!("Could not parse automaton, skipping... {:?}", e);
                        hoa = HoaString(hoa.0[pos + END_LEN..].trim_start().to_string());
                    }
                }
            }
            (Some(abort), None) => {
                trace!(
                    "Found only one automaton --ABORT--ed at {abort}, but no subsequent --END-- of automaton to parse."
                );
                return None;
            }
            (Some(abort), Some(end)) => {
                if abort < end {
                    trace!(
                        "Found --ABORT-- before --END--, returning first automaton from {abort} to {end}"
                    );
                    match parse_omega_automaton_range(&hoa.0, abort + ABORT_LEN, end + END_LEN) {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
                        }
                    }
                } else {
                    trace!("Found --END--, returning first automaton up to {end}");
                    match parse_omega_automaton_range(&hoa.0, 0, end + END_LEN) {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
                        }
                    }
                }
            }
            (None, None) => {
                trace!("No end of automaton found, there is no automaton to parse.");
                return None;
            }
        }
    }
}

/// Considers the given HOA string as a single automaton and tries to parse it into an
/// [`OmegaAutomaton`].
pub fn hoa_to_ts<const DET: bool>(hoa: &str) -> Vec<OmegaAutomaton<PropAlphabet, DET>> {
    let mut out = vec![];
    for hoa_aut in hoars::parse_hoa_automata(hoa) {
        match hoa_aut.try_into() {
            Ok(aut) => out.push(aut),
            Err(e) => tracing::warn!("Encountered parsing error {}", e),
        }
    }
    out
}

impl TryFrom<&hoars::Header> for OmegaAcceptanceCondition {
    type Error = String;

    fn try_from(value: &hoars::Header) -> Result<Self, Self::Error> {
        let acceptance_sets = value.iter().find_map(|it| match it {
            hoars::HeaderItem::Acceptance(acceptance, _cond) => Some(*acceptance),
            _ => None,
        });

        match value.acceptance_name() {
            hoars::AcceptanceName::Buchi => Ok(Self::Buchi),
            hoars::AcceptanceName::Parity => Ok(Self::Parity(0, acceptance_sets.unwrap() as Int)),
            _ => Err("Unsupported acceptance condition".to_string()),
        }
    }
}

impl<const DET: bool> TryFrom<HoaRepresentation> for OmegaAutomaton<PropAlphabet, DET> {
    type Error = String;
    fn try_from(value: HoaRepresentation) -> Result<Self, Self::Error> {
        hoa_automaton_to_ts(value)
    }
}

/// Converts a [`HoaRepresentation`] into a [`crate::NTS`] with the same semantics. This creates the appropriate
/// number of states and inserts transitions with the appropriate labels and colors.
pub fn hoa_automaton_to_ts<const DET: bool>(
    aut: HoaRepresentation,
) -> Result<OmegaAutomaton<PropAlphabet, DET>, String> {
    let aps = aut.num_aps();
    assert!(aps <= crate::hoa::MAX_APS);

    let alphabet = PropAlphabet::from_apnames(aut.aps().iter());
    let mut ts: crate::TS<PropAlphabet, Int, AcceptanceMask, DET> =
        crate::TS::for_alphabet(alphabet);

    for (id, state) in aut.body().iter().enumerate() {
        assert_eq!(id, state.id() as usize);
        assert_eq!(id, ts.add_state(state.id() as Int) as usize);
    }

    for state in aut.body().iter() {
        for edge in state.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .expect("Cannot yet deal with conjunctions of target states");
            let label = edge.label().deref().clone();

            let expr = label.try_into_hoa_expression(aps)?;
            let color: AcceptanceMask = edge.acceptance_signature().into();

            if ts
                .add_edge((state.id(), PropExpression::from_bdd(expr), color, target))
                .is_some()
            {
                // this thing is not deterministic, so we return
                if DET {
                    warn!("rejecting nondeterministic automaton");
                    return Err("Automaton is not deterministic".to_string());
                }
            }
        }
    }

    debug_assert!(!DET || ts.is_deterministic());

    let start = aut.start();
    assert_eq!(start.len(), 1);
    let initial = start[0]
        .get_singleton()
        .expect("Initial state must be a singleton");

    let acceptance: OmegaAcceptanceCondition = aut.header().try_into()?;

    Ok(OmegaAutomaton::from_parts_with_acceptance(
        ts, initial, acceptance,
    ))
}

#[cfg(test)]
mod tests {
    use tracing::debug;

    use crate::{TransitionSystem, hoa::HoaString};

    #[test]
    fn hoa_tdba_with_abort_and_nondeterministic() {
        let raw_hoa = r#"
        HOA: v1
        States: 3
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 1
        --ABORT--
        HOA: v1
        States: 2
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        State: 1
        [0] 0 {0}
        [0] 1
        [!0] 0
        --END--
        HOA: v1
        States: 1
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        --END--
        "#;
        let hoa = HoaString(raw_hoa.to_string());
        debug!("SADF");

        let first = super::pop_deterministic_omega_automaton(hoa);
        assert!(first.is_some());
        let (first, hoa) = first.unwrap();
        assert_eq!(first.size(), 1);
        assert!(hoa.0.is_empty());
    }
}
