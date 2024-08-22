use crate::ta::clock::Clock;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ClockComparator {
    LESSER,
    LEQ,
    GEQ,
    GREATER,
}

#[wasm_bindgen]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Clause {
    lhs: Clock,
    op: ClockComparator,
    rhs: u32,
}

#[wasm_bindgen]
impl Clause {
    #[wasm_bindgen(constructor)]
    pub fn new(lhs: &Clock, op: ClockComparator, rhs: u32) -> Self {
        Self {
            lhs: lhs.clone(),
            op,
            rhs,
        }
    }
}

impl Clause {
    pub fn lhs(&self) -> &Clock {
        &self.lhs
    }

    pub fn op(&self) -> ClockComparator {
        self.op
    }

    pub fn rhs(&self) -> u32 {
        self.rhs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_returns_correct_clause_when_called() {
        // given
        let clock = Clock::new("x");
        let op = ClockComparator::LESSER;
        let rhs = 42;

        // when
        let result = Clause::new(&clock, op, rhs);

        // then
        assert_eq!(result.lhs, clock);
        assert_eq!(result.op, op);
        assert_eq!(result.rhs, rhs);
    }
}
