use biodivine_lib_bdd::{Bdd, BddPartialValuation, BddVariable, BddVariableSet};
use itertools::Itertools;
use std::ops::Deref;

/// Newtype wrapper around a [`crate::LabelExpression`], implements [`Deref`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label(pub LabelExpression);

impl Deref for Label {
    type Target = LabelExpression;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum AbstractLabelExpression {
    Boolean(bool),
    Integer(u16),
    Negated(Box<AbstractLabelExpression>),
    Conjunction(Vec<AbstractLabelExpression>),
    Disjunction(Vec<AbstractLabelExpression>),
}

pub(crate) enum Atomic {
    Positive(u16),
    Negative(u16),
}

impl Atomic {
    pub(crate) fn to_value(&self, vars: &[BddVariable]) -> (BddVariable, bool) {
        match self {
            Self::Positive(i) => (vars[*i as usize], true),
            Self::Negative(i) => (vars[*i as usize], false),
        }
    }
}

impl AbstractLabelExpression {
    pub(crate) fn try_atom(&self) -> Option<Atomic> {
        match self {
            Self::Integer(i) => Some(Atomic::Positive(*i)),
            Self::Negated(bx) => match **bx {
                Self::Integer(i) => Some(Atomic::Negative(i)),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn try_into_prop(self, num_aps: u8) -> Result<HoaExpression, String> {
        let var_set = BddVariableSet::new_anonymous(num_aps as u16);
        let vars: Vec<_> = (0..num_aps)
            .map(|i| BddVariable::from_index(i as usize))
            .collect();
        let bdd = self.try_into_bdd(&var_set, &vars)?;
        Ok(bdd)
    }

    pub fn try_into_bdd(self, vs: &BddVariableSet, vars: &[BddVariable]) -> Result<Bdd, String> {
        match self {
            Self::Boolean(b) => Ok(match b {
                true => vs.mk_true(),
                false => vs.mk_false(),
            }),
            Self::Integer(i) => {
                if i < vs.num_vars() {
                    Ok(vs.mk_var(vars[i as usize]))
                } else {
                    Err(format!("AP identifier {i} is too high"))
                }
            }
            Self::Negated(e) => Ok(e.try_into_bdd(vs, vars)?.not()),
            Self::Conjunction(cs) => {
                if let Some(ints) = cs.iter().map(|c| c.try_atom()).collect::<Option<Vec<_>>>() {
                    let valuation = BddPartialValuation::from_values(
                        &ints.into_iter().map(|a| a.to_value(vars)).collect_vec(),
                    );
                    Ok(vs.mk_conjunctive_clause(&valuation))
                } else {
                    Err(format!(
                        "could not parse label expression conjunct {cs:?}, expected atom"
                    ))
                }
            }
            Self::Disjunction(ds) => {
                if let Some(ints) = ds.iter().map(|c| c.try_atom()).collect::<Option<Vec<_>>>() {
                    let valuation = BddPartialValuation::from_values(
                        &ints.into_iter().map(|a| a.to_value(vars)).collect_vec(),
                    );
                    Ok(vs.mk_disjunctive_clause(&valuation))
                } else {
                    Err(format!(
                        "could not parse label expression disjunct {ds:?}, expected atom"
                    ))
                }
            }
        }
    }
}

pub const MAX_APS: u8 = 6;
pub type HoaRepr = u8;
/// Typedef for an alphabet used by a [`crate::HoaRepresentation`].
#[allow(unused)]
pub struct HoaAlphabet(Vec<String>);

impl FromIterator<String> for HoaAlphabet {
    fn from_iter<T: IntoIterator<Item = String>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// Typedef for an expression used by a [`crate::HoaRepresentation`].
pub type HoaExpression = Bdd;

/// Typedef for a symbol used by a [`crate::HoaRepresentation`].
pub type HoaSymbol = Vec<HoaRepr>;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum LabelExpression {
    Expression(HoaExpression),
    Abstract(AbstractLabelExpression),
}

impl LabelExpression {
    pub fn try_into_hoa_expression(self, num_aps: u8) -> Result<HoaExpression, String> {
        match self {
            Self::Expression(b) => Ok(b),
            Self::Abstract(b) => b.try_into_prop(num_aps),
        }
    }
}
pub fn build_vars(count: u16) -> (BddVariableSet, Vec<BddVariable>) {
    let vs = BddVariableSet::new_anonymous(count);
    let vars = vs.variables().into_iter().take(count as usize).collect();
    (vs, vars)
}

#[cfg(test)]
#[allow(unused)]
pub(crate) struct Anonymous<const PARSED: bool = false>;
#[cfg(test)]
#[allow(unused)]
pub(crate) type AnonymousParsed = Anonymous<true>;
#[cfg(test)]
#[allow(unused)]
pub(crate) type AnonymousAbstract = Anonymous<false>;

#[cfg(test)]
#[allow(unused)]
use AbstractLabelExpression::*;

#[cfg(test)]
#[allow(unused)]
#[allow(dead_code)]
impl Anonymous<false> {
    pub fn var_expr(n: u16) -> LabelExpression {
        assert!(n < MAX_APS as u16);
        LabelExpression::Abstract(AbstractLabelExpression::Integer(n))
    }
    pub fn not_var_expr(n: u16) -> LabelExpression {
        assert!(n < MAX_APS as u16);
        LabelExpression::Abstract(Negated(Box::new(Integer(n))))
    }
    pub fn top_label() -> Label {
        Label(LabelExpression::Abstract(AbstractLabelExpression::Boolean(
            true,
        )))
    }
    pub fn var_label(n: u16) -> Label {
        assert!(n < MAX_APS as u16);
        Label(Self::var_expr(n))
    }
    pub fn not_var_label(n: u16) -> Label {
        assert!(n < MAX_APS as u16);
        Label(Self::not_var_expr(n))
    }
}

#[cfg(test)]
#[allow(unused)]
#[allow(dead_code)]
impl Anonymous<true> {
    pub fn var_expr(n: usize) -> LabelExpression {
        assert!(n < MAX_APS as usize);
        LabelExpression::Expression(Self::var(n))
    }
    pub fn var_label(n: usize) -> Label {
        assert!(n < MAX_APS as usize);
        Label(Self::var_expr(n))
    }
    pub fn var(n: usize) -> Bdd {
        assert!(n < MAX_APS as usize);
        BddVariableSet::new_anonymous(MAX_APS as u16).mk_var(BddVariable::from_index(n))
    }
    pub fn not_var(n: usize) -> Bdd {
        assert!(n < MAX_APS as usize);
        BddVariableSet::new_anonymous(MAX_APS as u16).mk_not_var(BddVariable::from_index(n))
    }
    pub fn top() -> Bdd {
        BddVariableSet::new_anonymous(MAX_APS as u16).mk_true()
    }
    pub fn top_expr() -> LabelExpression {
        LabelExpression::Expression(Self::top())
    }
    pub fn top_label() -> Label {
        Label(Self::top_expr())
    }
}
