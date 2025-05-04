use std::fmt::Display;

use itertools::Itertools;

use crate::{
    AcceptanceAtom, AcceptanceCondition, AcceptanceInfo, AcceptanceName, AcceptanceSignature,
    AliasName, Edge, HeaderItem, HoaBool, HoaRepresentation, Label, Property, State,
    StateConjunction,
};

pub fn to_hoa(aut: &HoaRepresentation) -> String {
    aut.header()
        .into_iter()
        .map(|header_item| header_item.to_string())
        .chain(std::iter::once("--BODY--".to_string()))
        .chain(aut.body().into_iter().map(|state| state.to_string()))
        .chain(std::iter::once("--END--".to_string()))
        .join("\n")
}

impl Display for HeaderItem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Version(version) => write!(f, "HOA: {}", version),
            Self::States(number) => write!(f, "States: {}", number),
            Self::Start(state_conj) => write!(f, "Start: {}", state_conj),
            Self::AP(aps) => write!(
                f,
                "AP: {} {}",
                aps.len(),
                aps.iter().map(|ap| format!("\"{}\"", ap)).join(" ")
            ),
            Self::Alias(alias_name, alias_expression) => {
                write!(f, "Alias: {} {}", alias_name, alias_expression)
            }
            Self::Acceptance(number_sets, condition) => {
                write!(f, "Acceptance: {} {}", number_sets, condition)
            }
            Self::AcceptanceName(identifier, vec_info) => {
                write!(f, "acc-name: {} {}", identifier, vec_info.iter().join(" "))
            }
            Self::Tool(name, options) => {
                write!(f, "tool: {} {}", name, options.iter().join(" "))
            }
            Self::Name(name) => write!(f, "name: {}", name),
            Self::Properties(properties) => {
                write!(f, "properties: {}", properties.iter().join(" "))
            }
        }
    }
}

impl Display for AcceptanceInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(integer) => write!(f, "{}", integer),
            Self::Identifier(identifier) => write!(f, "{}", identifier),
        }
    }
}

impl Display for Property {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::StateLabels => "state-labels",
                Self::TransLabels => "trans-labels",
                Self::ImplicitLabels => "implicit-labels",
                Self::ExplicitLabels => "explicit-labels",
                Self::StateAcceptance => "state-acc",
                Self::TransitionAcceptance => "trans-acc",
                Self::UniversalBranching => "univ-branch",
                Self::NoUniversalBranching => "no-univ-branch",
                Self::Deterministic => "deterministic",
                Self::Complete => "complete",
                Self::Unambiguous => "unabmiguous",
                Self::StutterInvariant => "stutter-invariant",
                Self::Weak => "weak",
                Self::VeryWeak => "very-weak",
                Self::InherentlyWeak => "inherently-weak",
                Self::Terminal => "terminal",
                Self::Tight => "tight",
                Self::Colored => "colored",
            }
        )
    }
}

impl Display for AcceptanceName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Buchi => "Buchi",
                Self::GeneralizedBuchi => "generalized-Buchi",
                Self::CoBuchi => "co-Buchi",
                Self::GeneralizedCoBuchi => "generalized-co-Buchi",
                Self::Streett => "Streett",
                Self::Rabin => "Rabin",
                Self::GeneralizedRabin => "generalized-Rabin",
                Self::Parity => "parity",
                Self::All => "all",
                Self::None => "none",
            }
        )
    }
}

impl Display for AcceptanceAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Positive(id) => write!(f, "{}", id),
            Self::Negative(id) => write!(f, "!{}", id),
        }
    }
}

impl Display for HoaBool {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.0 { "t" } else { "f" })
    }
}

impl Display for AcceptanceCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fin(id) => write!(f, "Fin({})", id),
            Self::Inf(id) => write!(f, "Inf({})", id),
            Self::And(left, right) => write!(f, "({} & {})", left, right),
            Self::Or(left, right) => write!(f, "({} | {})", left, right),
            Self::Boolean(val) => write!(f, "{}", val),
        }
    }
}

impl Display for AliasName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl Display for StateConjunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0.iter().map(|s| s.to_string()).join(" & "))
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{:?}]", self.0)
    }
}

impl Display for AcceptanceSignature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return Ok(());
        }
        write!(f, "{{{}}}", self.0.iter().join(" "))
    }
}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} {}", self.0, self.1, self.2)
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(acc) = &self.1 {
            writeln!(f, "State: {} \"{}\"", self.0, acc)?;
        } else {
            writeln!(f, "State: {}", self.0)?;
        }
        for edge in &self.2 {
            writeln!(f, "{}", edge)?;
        }
        Ok(())
    }
}
