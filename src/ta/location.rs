use crate::ta::clock_constraint::ClockConstraint;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Location {
    name: String,
    is_initial: bool,
    invariant: Option<ClockConstraint>,
}

#[wasm_bindgen]
impl Location {
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str, is_initial: bool, invariant: Option<ClockConstraint>) -> Self {
        Self {
            name: String::from(name),
            is_initial,
            invariant,
        }
    }
}

impl Location {
    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn is_initial(&self) -> bool {
        self.is_initial
    }

    pub fn invariant(&self) -> &Option<ClockConstraint> {
        &self.invariant
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock::Clock;
    use crate::ta::clock_constraint::clause::{Clause, ClockComparator};

    #[test]
    fn new_returns_correct_location_when_called() {
        // given
        let name = "init";
        let is_initial = true;
        let clause = Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42);
        let clauses = Box::from([clause]);
        let cc = ClockConstraint::new(clauses);

        // when
        let result = Location::new(name, is_initial, Some(cc.clone()));

        // then
        assert_eq!(result.name, name);
        assert_eq!(result.is_initial, is_initial);
        assert_eq!(result.invariant, Some(cc));
    }
}
