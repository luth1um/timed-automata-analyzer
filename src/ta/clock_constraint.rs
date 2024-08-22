use crate::ta::clock_constraint::clause::Clause;
use crate::util::vecs_eq_without_order;
use wasm_bindgen::prelude::wasm_bindgen;

pub mod clause;

#[wasm_bindgen]
#[derive(Debug, Clone, Eq)]
pub struct ClockConstraint {
    clauses: Vec<Clause>,
}

#[wasm_bindgen]
impl ClockConstraint {
    #[wasm_bindgen(constructor)]
    pub fn new(clauses: Box<[Clause]>) -> Self {
        Self {
            clauses: Vec::from(clauses),
        }
    }
}

impl ClockConstraint {
    pub fn clauses(&self) -> &Vec<Clause> {
        &self.clauses
    }
}

impl PartialEq<Self> for ClockConstraint {
    fn eq(&self, other: &Self) -> bool {
        vecs_eq_without_order(&self.clauses, &other.clauses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock::Clock;
    use crate::ta::clock_constraint::clause::ClockComparator;

    #[test]
    fn new_returns_correct_constraint_when_called() {
        // given
        let clause = Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42);
        let clauses = Box::from([clause.clone()]);

        // when
        let result = ClockConstraint::new(clauses);

        // then
        let result_clauses = result.clauses();
        assert_eq!(result_clauses.len(), 1);
        assert_eq!(result_clauses.get(0), Some(&clause));
    }

    #[test]
    fn eq_returns_true_when_constraints_contain_same_clauses() {
        // given
        let clause0 = Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42);
        let clause1 = Clause::new(&Clock::new("y"), ClockComparator::GEQ, 12);
        let clauses0 = Box::from([clause0.clone(), clause1.clone()]);
        let clauses1 = Box::from([clause1.clone(), clause0.clone()]);
        let cc0 = ClockConstraint::new(clauses0);
        let cc1 = ClockConstraint::new(clauses1);

        // when / then
        assert_eq!(cc0, cc1);
    }

    #[test]
    fn eq_returns_false_when_clauses_have_different_elements() {
        // given
        let clause0 = Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42);
        let clause1 = Clause::new(&Clock::new("y"), ClockComparator::GEQ, 12);
        let clauses0 = Box::from([clause0.clone()]);
        let clauses1 = Box::from([clause1.clone()]);
        let cc0 = ClockConstraint::new(clauses0);
        let cc1 = ClockConstraint::new(clauses1);

        // when / then
        assert_ne!(cc0, cc1);
    }

    #[test]
    fn eq_is_reflexive() {
        // given
        let a = ClockConstraint {
            clauses: vec![Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42)],
        };

        // when / then
        assert_eq!(a, a);
    }

    #[test]
    fn eq_is_symmetric() {
        // given
        let a = ClockConstraint {
            clauses: vec![Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42)],
        };
        let b = a.clone();

        // when / then
        assert!(!(a == b) || b == a);
    }

    #[test]
    fn eq_is_transitive() {
        // given
        let a = ClockConstraint {
            clauses: vec![Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42)],
        };
        let b = a.clone();
        let c = a.clone();

        // when / then
        assert!(!(a == b && b == c) || a == c);
    }
}
