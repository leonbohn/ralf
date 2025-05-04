use itertools::Itertools;
use tracing::trace;

use std::fmt::{Result, Write};

use crate::{
    Pointed, TransitionSystem,
    automaton::{DBA, DPA, OmegaAcceptanceCondition},
    core::{
        Int, Show,
        alphabet::{Alphabet, CharAlphabet, PropAlphabet},
    },
    ts::{EdgeColor, EdgeExpression, IsEdge},
};

pub trait WriteHoa: TransitionSystem + Pointed {
    fn write_hoa<W: Write>(&self, w: &mut W) -> Result {
        w.write_str("HOA: v1\n")?;

        self.write_alphabet_description(w)?;

        w.write_fmt(format_args!("States: {}\n", self.size()))?;

        w.write_str("Start: ")?;
        self.write_state_id(w, self.initial())?;
        w.write_char('\n')?;

        self.write_acceptance(w)?;

        w.write_str("--BODY--")?;

        for state in self.state_indices() {
            w.write_str("\nState: ")?;
            self.write_state_id(w, state)?;
            for edge in self.edges_from(state).expect("We know this state exists") {
                w.write_char('\n')?;
                w.write_char('[')?;
                self.write_expression(w, edge.expression())?;
                w.write_char(']')?;
                w.write_char(' ')?;

                self.write_state_id(w, edge.target())?;

                w.write_char(' ')?;
                self.write_edge_color(w, edge.color())?;
            }
        }

        w.write_str("\n--END--\n")?;

        Ok(())
    }

    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result;

    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result;

    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result;

    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result;

    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result;

    fn to_hoa(&self) -> String {
        let mut w = String::new();
        self.write_hoa(&mut w).unwrap();
        trace!("produced HOA string from automaton\n{}", w);
        w
    }
}

impl OmegaAcceptanceCondition {
    pub fn write_hoa<W: Write>(&self, w: &mut W) -> Result {
        match self {
            Self::Parity(low, high) => {
                let zero_based_range = high - low + (low % 2);
                write!(
                    w,
                    "acc-name: parity min even {}\nAcceptance: {} {}\n",
                    zero_based_range + 1,
                    zero_based_range + 1,
                    build_parity_condition_hoa(*low, *high)
                )
            }
            Self::Buchi => {
                write!(w, "acc-name: Buchi\nAcceptance: 1 Inf(0)\n")
            }
            _ => todo!("Can not yet deal with other acceptance types"),
        }
    }
}

pub trait HoaSuitableAlphabet: Alphabet {
    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result;
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result;
}

impl<A: HoaSuitableAlphabet> WriteHoa for DBA<A> {
    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result {
        if label {
            write!(w, "{{{}}}", 0)
        } else {
            write!(w, "{{{}}}", 1)
        }
    }

    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result {
        self.alphabet().write_expression(w, expr)
    }

    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result {
        write!(w, "{}", id)
    }

    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        self.alphabet().write_alphabet_description(w)
    }

    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        OmegaAcceptanceCondition::Buchi.write_hoa(w)
    }
}

impl<A: HoaSuitableAlphabet> WriteHoa for DPA<A> {
    fn write_edge_color<W: std::fmt::Write>(&self, w: &mut W, label: EdgeColor<Self>) -> Result {
        write!(w, "{{{}}}", label)
    }

    fn write_expression<W: std::fmt::Write>(
        &self,
        w: &mut W,
        expr: &EdgeExpression<Self>,
    ) -> Result {
        self.alphabet().write_expression(w, expr)
    }

    fn write_state_id<W: std::fmt::Write>(
        &self,
        w: &mut W,
        id: Self::StateIndex,
    ) -> std::fmt::Result {
        write!(w, "{}", id)
    }

    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        self.alphabet().write_alphabet_description(w)
    }

    fn write_acceptance<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        let (low, high) = self.low_and_high_priority();

        OmegaAcceptanceCondition::Parity(low, high).write_hoa(w)
    }
}

impl HoaSuitableAlphabet for CharAlphabet {
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        writeln!(
            w,
            "AP: {} {}",
            self.size(),
            (0..self.size())
                .map(|i| ((b'a') + (i as u8)) as char)
                .map(|c| format!("\"{}\"", c))
                .join(" ")
        )
    }

    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
        write!(
            w,
            "{}",
            (0..self.size())
                .map(|i| if i as u8 == (*expr as u8) - (b'a') {
                    format!("{i}")
                } else {
                    format!("!{i}")
                })
                .join(" & ")
        )
    }
}

impl HoaSuitableAlphabet for PropAlphabet {
    fn write_alphabet_description<W: std::fmt::Write>(&self, w: &mut W) -> Result {
        writeln!(
            w,
            "AP: {} {}",
            self.aps(),
            self.apnames()
                .iter()
                .map(|name| format!("\"{}\"", name))
                .join(" ")
        )
    }

    fn write_expression<W: std::fmt::Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
        write!(w, "{}", expr.show())
    }
}

/// Assumes that `low` is the least occurring and `high` is the highest occurring priority,
/// *inclusive*.
fn build_parity_condition_hoa(low: Int, high: Int) -> String {
    let parity = low % 2;

    if high <= low {
        return match parity {
            0 => "t".to_string(),
            1 => "f".to_string(),
            _ => unreachable!(),
        };
    }

    match high - low {
        0 => match parity {
            0 => format!("Inf({low})"),
            1 => format!("Fin({low})"),
            _ => unreachable!(),
        },
        1 => match parity {
            0 => format!("Inf({low}) | Fin({high})"),
            1 => format!("Fin({low}) & Inf({high})"),
            _ => unreachable!(),
        },
        _ => match parity {
            0 => format!(
                "Inf({low}) | ({})",
                build_parity_condition_hoa(low + 1, high)
            ),
            1 => format!(
                "Fin({low}) & ({})",
                build_parity_condition_hoa(low + 1, high)
            ),
            _ => unreachable!(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::WriteHoa;
    use crate::ts::TSBuilder;

    #[test]
    fn build_parity_hoa_string() {
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(0, 4),
            "Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))"
        );
        assert_eq!(
            crate::hoa::output::build_parity_condition_hoa(0, 2),
            "Inf(0) | (Fin(1) & Inf(2))"
        );
    }

    #[test]
    fn write_hoa_dpa() {
        let dpa = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', 0, 0), (0, 'b', 1, 0), (0, 'c', 2, 0)])
            .into_dpa(0);
        let hoa = dpa.to_hoa();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: parity min even 3\nAcceptance: 3 Inf(0) | (Fin(1) & Inf(2))\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {2}\n--END--\n"
        );
    }

    #[test]
    fn write_hoa_dba() {
        let dba = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0), (0, 'c', true, 0)])
            .into_dba(0);
        let hoa = dba.to_hoa();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {0}\n--END--\n"
        );
    }
}
