#![allow(missing_docs)]

use std::{
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
    sync::{Arc, Mutex},
};

use biodivine_lib_bdd::{
    Bdd, BddPartialValuation, BddSatisfyingValuations, BddValuation, BddVariableSet,
};
use itertools::Itertools;
use tracing::trace;

use crate::{math::OrderedSet, show::Show};

use super::{Alphabet, CharAlphabet, Expression, Matcher};

pub trait RawSymbolRepr: std::fmt::Debug + Hash + Eq + Ord + Copy {
    fn as_usize(&self) -> usize;
    fn from_usize(from: usize) -> Self;
    fn bit(&self, n: usize) -> bool;
    fn set(&mut self, n: usize);
    fn max_aps() -> usize;
}

macro_rules! impl_raw_symbol_repr {
    ($($ty:ty),*) => {
        $(
            impl RawSymbolRepr for $ty {
                fn max_aps() -> usize {
                    std::mem::size_of::<$ty>() * 8
                }
                fn as_usize(&self) -> usize {
                    *self as usize
                }
                fn from_usize(from: usize) -> Self {
                    from.try_into().unwrap()
                }
                fn bit(&self, n: usize) -> bool {
                    assert!(n <= Self::max_aps());
                    *self & (1 << n) != 0
                }
                fn set(&mut self, n: usize) {
                    assert!(n <= Self::max_aps());
                    *self |= 1 << n;
                }
            }
        )*
    }
}
impl_raw_symbol_repr!(u8, u16, u32, u64, u128, usize);

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct PropSymbol<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    raw: RawTy,
}

impl<RawTy: RawSymbolRepr> PropSymbol<RawTy> {
    pub fn as_expression(&self) -> PropExpression<RawTy> {
        PropExpression::from_parts(self.num_aps, self.as_bdd_valuation().into())
    }
    pub fn as_char(&self) -> char {
        (b'a' + ((self.raw.as_usize() as u8) & 0b1111)) as char
    }
    pub fn from_char(value: char, aps: usize) -> Self {
        assert!(aps <= RawTy::max_aps());
        let val = value as u8;
        assert!(b'a' <= val);
        assert!(val < b'p');

        Self {
            raw: RawTy::from_usize(((val - b'a') & 0b1111) as usize),
            num_aps: aps.try_into().unwrap(),
        }
    }
    pub fn as_bools(&self) -> Vec<bool> {
        assert!(
            self.num_aps as usize <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32)
        );

        let out = (0..self.num_aps).rev().fold(
            Vec::with_capacity(self.num_aps as usize),
            |mut acc, x| {
                acc.push(self.raw.bit(x as usize));
                acc
            },
        );
        trace!("got {out:?} from {self:?}");
        out
    }
    pub fn from_bools(bools: Vec<bool>) -> Self {
        assert!(bools.len() <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32));
        let mut raw = RawTy::from_usize(0);

        (0..bools.len()).rev().for_each(|i| {
            if bools[i] {
                raw.set(i)
            }
        });
        trace!("got {:?} from bools {:?}", raw, bools);

        Self {
            num_aps: bools.len() as u8,
            raw,
        }
    }
    pub fn as_bdd_valuation(&self) -> BddValuation {
        BddValuation::new(self.as_bools())
    }
    pub fn from_bdd_valuation(val: BddValuation) -> Self {
        Self::from_bools(val.vector())
    }
}

impl<RawTy: RawSymbolRepr> Show for PropSymbol<RawTy> {
    fn show(&self) -> String {
        let chr = |b| {
            if b { '1' } else { '0' }
        };
        assert!(
            self.num_aps as usize <= 8usize.saturating_pow(std::mem::size_of::<RawTy>() as u32)
        );
        (0..self.num_aps).rev().fold(
            String::with_capacity(self.num_aps as usize),
            |mut acc, x| {
                acc.push(chr(self.raw.bit(x as usize)));
                acc
            },
        )
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct PropExpression<RawTy: RawSymbolRepr = u32> {
    num_aps: u8,
    bdd: Bdd,
    _ty: PhantomData<RawTy>,
}

impl<RawTy: RawSymbolRepr> PropExpression<RawTy> {
    pub fn from_parts(num_aps: u8, bdd: Bdd) -> Self {
        Self {
            num_aps,
            bdd,
            _ty: PhantomData,
        }
    }
    pub fn new(num_aps: u8, string: &str) -> Self {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self::from_parts(num_aps, vars.eval_expression_string(string))
    }
    pub fn into_bdd(self) -> Bdd {
        self.bdd
    }
    pub fn universal(num_aps: u8) -> Self {
        let vars = BddVariableSet::new_anonymous(num_aps as u16);
        Self {
            num_aps,
            bdd: vars.mk_true(),
            _ty: PhantomData,
        }
    }
    pub fn sat_vals(&self) -> PropExpressionSymbols<'_, RawTy> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData,
        }
    }
    pub fn from_bdd(bdd: Bdd) -> Self {
        Self {
            num_aps: bdd
                .num_vars()
                .try_into()
                .expect("Number of variables does not fit into u8"),
            bdd,
            _ty: PhantomData,
        }
    }
    pub fn chars_iter(&self) -> impl Iterator<Item = char> + '_ {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData,
        }
        .map(|e: PropSymbol<RawTy>| e.as_char())
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAnd for PropExpression<RawTy> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        Self {
            num_aps: self.num_aps,
            bdd: self.bdd.and(&rhs.bdd),
            _ty: PhantomData,
        }
    }
}
impl<RawTy: RawSymbolRepr> std::ops::Not for PropExpression<RawTy> {
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::from_parts(self.num_aps, self.bdd.not())
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOr for PropExpression<RawTy> {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        assert_eq!(self.num_aps, rhs.num_aps);
        Self::from_parts(self.num_aps, self.bdd.or(&rhs.bdd))
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitAndAssign for PropExpression<RawTy> {
    fn bitand_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        *self = Self::from_parts(self.num_aps, self.bdd.and(&rhs.bdd));
    }
}

impl<RawTy: RawSymbolRepr> std::ops::BitOrAssign for PropExpression<RawTy> {
    fn bitor_assign(&mut self, rhs: Self) {
        assert_eq!(self.num_aps, rhs.num_aps);
        *self = Self::from_parts(self.num_aps, self.bdd.or(&rhs.bdd));
    }
}

impl<RawTy: RawSymbolRepr> PartialOrd for PropExpression<RawTy> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<RawTy: RawSymbolRepr> Ord for PropExpression<RawTy> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.bdd
            .sat_valuations()
            .min()
            .cmp(&other.bdd.sat_valuations().min())
    }
}

fn clause_to_string(clause: &BddPartialValuation) -> String {
    let offset = |x| (b'a' + x as u8) as char;
    let mut vals = clause.to_values();
    vals.sort();
    vals.into_iter()
        .map(|(v, b)| {
            if b {
                offset(v.to_index()).to_string()
            } else {
                format!("!{}", offset(v.to_index()))
            }
        })
        .join("&")
}

impl<RawTy: RawSymbolRepr> Show for PropExpression<RawTy> {
    fn show(&self) -> String {
        let dnf = self.bdd.to_optimized_dnf();
        let clauses = dnf.len();

        if clauses > 1 {
            let mut out = format!("({})", clause_to_string(&dnf[0]));

            for clause in &dnf {
                out.push_str(&format!(" | ({})", clause_to_string(clause)));
            }

            out
        } else {
            clause_to_string(&dnf[0])
        }
    }
}

impl<RawTy: RawSymbolRepr> Matcher<PropExpression<RawTy>> for PropSymbol<RawTy> {
    fn matches(&self, expression: &PropExpression<RawTy>) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        expression.bdd.eval_in(&self.as_bdd_valuation())
    }
}

impl<RawTy: RawSymbolRepr> Matcher<Self> for PropExpression<RawTy> {
    fn matches(&self, expression: &Self) -> bool {
        assert_eq!(self.num_aps, expression.num_aps);
        // all values in self should also be in expression
        // we share nothing with the complement of the expression
        expression.bdd.not().and(&self.bdd).sat_witness().is_none()
    }
}

impl<RawTy: RawSymbolRepr> Expression for PropExpression<RawTy> {
    type S = PropSymbol<RawTy>;

    type SymbolsIter<'this>
        = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn symbols(&self) -> Self::SymbolsIter<'_> {
        PropExpressionSymbols {
            iter: self.bdd.sat_valuations(),
            _ty: PhantomData::<RawTy>,
        }
    }

    fn overlaps(&self, _other: &Self) -> bool {
        todo!()
    }
}

pub struct PropExpressionSymbols<'a, RawTy: RawSymbolRepr> {
    iter: BddSatisfyingValuations<'a>,
    _ty: PhantomData<RawTy>,
}

impl<RawTy: RawSymbolRepr> Iterator for PropExpressionSymbols<'_, RawTy> {
    type Item = PropSymbol<RawTy>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(PropSymbol::from_bdd_valuation(self.iter.next()?))
    }
}

/// Represents a propositional alphabet, which consists of a list of atomic propositions.
///
/// A symbol of this alphabet simply a valuation of the atomic propositions, which is
/// represented as a binary string of length `num_aps` (whose limit gets determined by
/// the number of bits in the type parameter `RawTy`).
///
/// An Expression is represented by a boolean formula over the atomic propositions. Here,
/// we store it as a [`PropExpression`] which in turn contains a [`Bdd`].
///
/// # Example
/// Assume we have a propositional alphabet over the atomic propositions `a`, `b` and `c`.
///
/// Then a **symbol** in this alphabet is a valuation of these variables, e.g. `a & !b & c`.
///
/// An **expression** on the other hand is used to label edges and it is a boolean expression over
/// the atomic propositions, e.g. `(a | b) & c`. Such an expression is matched by
/// a symbol if the symbol satisfies the expression, i.e. if the expression evaluates to `true` under the given
/// valuation. The expression from above, for example, would be matched by the symbol given above (`a & !b & c`),
/// but not by the symbols `a & b & !c` or `!a & !b & c`.
#[derive(Clone, Debug)]
pub struct PropAlphabet<RawTy: RawSymbolRepr = u32> {
    aps: Vec<String>,
    universal: PropExpression<RawTy>,
    expressions: Arc<Mutex<OrderedSet<PropExpression<RawTy>>>>,
}

impl<RawTy: RawSymbolRepr> PropAlphabet<RawTy> {
    pub fn new(aps: Vec<String>) -> Self {
        assert!(aps.len() < RawTy::max_aps());
        assert!(!aps.is_empty());

        let universal = PropExpression::<RawTy>::universal(aps.len() as u8);
        Self {
            expressions: Arc::new(Mutex::new(OrderedSet::from_iter([universal.clone()]))),
            universal,
            aps,
        }
    }

    pub fn aps(&self) -> u8 {
        self.aps.len() as u8
    }

    pub fn char_to_symbol(&self, value: char) -> PropSymbol<RawTy> {
        assert!(value >= 'a');

        let raw = RawTy::from_usize(((value as u8) - b'a') as usize);
        PropSymbol {
            raw,
            num_aps: self.aps(),
        }
    }

    pub fn hoa_symbol_to_char(&self, sym: &PropSymbol<RawTy>) -> char {
        assert_eq!(sym.num_aps, self.aps(), "symbol does not match alphabet");
        assert!((sym.num_aps as usize) < RawTy::max_aps(), "too many aps");

        (b'a' + (sym.raw.as_usize() as u8)) as char
    }

    pub fn size(&self) -> usize {
        2u32.saturating_pow(self.aps() as u32)
            .try_into()
            .expect("Cannot fit value into usize")
    }
    pub fn apnames(&self) -> &[String] {
        &self.aps
    }

    /// Attempts to build an instance of `Self` from the given pointer to a [`CharAlphabet`]. This
    /// only works (for the moment) if the number of symbols in the given alphabet is an exact
    /// power of two.
    pub fn try_from_char_alphabet(value: &CharAlphabet) -> Result<Self, String> {
        let alphabet_size = value.size();
        if alphabet_size != alphabet_size.next_power_of_two() || alphabet_size == 0 {
            return Err(format!(
                "Alphabet size is not a power of two: {alphabet_size}"
            ));
        }

        let aps = alphabet_size.ilog2() as u8;
        assert!(aps > 0, "We do not want this edge case");

        Ok(Self::from_apnames(
            (0u8..aps).map(|i| ((b'a' + i) as char).to_string()),
        ))
    }

    pub fn from_apnames<I>(apnames: I) -> Self
    where
        I: IntoIterator,
        I::Item: Display,
    {
        let apnames: Vec<_> = apnames.into_iter().map(|i| i.to_string()).collect();
        Self::new(apnames)
    }
}

impl<RawTy: RawSymbolRepr> Alphabet for PropAlphabet<RawTy> {
    type Symbol = PropSymbol<RawTy>;

    type Expression = PropExpression<RawTy>;

    fn make_expression(&self, symbol: Self::Symbol) -> Self::Expression {
        let expr = PropExpression {
            bdd: Bdd::from(symbol.as_bdd_valuation()),
            num_aps: symbol.num_aps,
            _ty: PhantomData,
        };
        let mut expressions = self.expressions.lock().unwrap();
        expressions.insert(expr.clone());
        expr
    }

    fn overlapping(&self, left: &Self::Expression, right: &Self::Expression) -> bool {
        assert_eq!(left.num_aps, right.num_aps);
        left.bdd.and(&right.bdd).sat_witness().is_some()
    }

    type Universe<'this>
        = PropExpressionSymbols<'this, RawTy>
    where
        Self: 'this;

    fn universe(&self) -> Self::Universe<'_> {
        self.universal.sat_vals()
    }

    fn contains(&self, _symbol: Self::Symbol) -> bool {
        unimplemented!()
    }

    fn size(&self) -> usize {
        2usize.saturating_pow(self.aps.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prop_symbol() {
        let ps = PropSymbol {
            num_aps: 5,
            raw: 19u32,
        };
        assert_eq!(ps.show(), "10011".to_string());
    }

    #[test]
    fn prop_expression() {
        let pe = PropExpression::<u32>::new(3, "x_0 | (x_1 & x_2)");

        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(PropSymbol::from_bools(vec![false, true, true]).matches(&pe));
        assert!(!PropSymbol::from_bools(vec![false, false, false]).matches(&pe));
    }
}
