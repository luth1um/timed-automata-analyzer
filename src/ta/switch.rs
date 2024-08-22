use crate::ta::clock::Clock;
use crate::ta::clock_constraint::ClockConstraint;
use crate::ta::location::Location;
use crate::util::vecs_eq_without_order;
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
#[derive(Debug, Clone, Eq)]
pub struct Switch {
    source: Location,
    guard: Option<ClockConstraint>,
    action: String,
    reset: Vec<Clock>,
    target: Location,
}

#[wasm_bindgen]
impl Switch {
    #[wasm_bindgen(constructor)]
    pub fn new(
        source: &Location,
        guard: Option<ClockConstraint>,
        action: &str,
        reset: Box<[Clock]>,
        target: &Location,
    ) -> Self {
        Self {
            source: source.clone(),
            guard,
            action: String::from(action),
            reset: Vec::from(reset),
            target: target.clone(),
        }
    }
}

impl Switch {
    pub fn source(&self) -> &Location {
        &self.source
    }

    pub fn guard(&self) -> &Option<ClockConstraint> {
        &self.guard
    }

    pub fn action(&self) -> &String {
        &self.action
    }

    pub fn reset(&self) -> &Vec<Clock> {
        &self.reset
    }

    pub fn target(&self) -> &Location {
        &self.target
    }
}

impl PartialEq<Self> for Switch {
    fn eq(&self, other: &Self) -> bool {
        self.action == other.action
            && vecs_eq_without_order(&self.reset, &other.reset)
            && self.guard == other.guard
            && self.source == other.source
            && self.target == other.target
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock_constraint::clause::{Clause, ClockComparator};

    #[test]
    fn new_returns_correct_switch_when_called() {
        // given
        let source = Location::new("loc0", true, None);
        let target = Location::new("loc1", false, None);
        let clause = Clause::new(&Clock::new("x"), ClockComparator::LESSER, 42);
        let cc = ClockConstraint::new(Box::from([clause]));
        let action = "action";
        let reset = vec![Clock::new("clock0"), Clock::new("clock1")];

        // when
        let result = Switch::new(
            &source,
            Some(cc.clone()),
            action,
            Box::from(reset.clone()),
            &target,
        );

        // then
        assert_eq!(result.source, source);
        assert_eq!(result.guard, Some(cc));
        assert_eq!(result.action, action);
        assert_eq!(result.reset, reset);
        assert_eq!(result.target, target);
    }

    #[test]
    fn eq_returns_true_when_switches_are_eq() {
        // given
        let sw0 = gen_switch();
        let sw1 = sw0.clone();

        // when / then
        assert_eq!(sw0, sw1);
    }

    #[test]
    fn eq_returns_false_when_sources_are_different() {
        // given
        let sw0 = gen_switch();
        let other_source = Location::new("different", false, None);
        let sw1 = Switch {
            source: other_source,
            ..gen_switch()
        };

        // when / then
        assert_ne!(sw0, sw1);
    }

    #[test]
    fn eq_returns_false_when_guards_are_different() {
        // given
        let sw0 = gen_switch();

        let clock_other = Clock::new("other");
        let clause = Clause::new(&clock_other, ClockComparator::GEQ, 1234);
        let cc = ClockConstraint::new(Box::from([clause]));
        let sw1 = Switch {
            guard: Some(cc),
            ..gen_switch()
        };

        // when / then
        assert_ne!(sw0, sw1);
    }

    #[test]
    fn eq_returns_false_when_actions_are_different() {
        // given
        let sw0 = gen_switch();
        let sw1 = Switch {
            action: String::from("other"),
            ..gen_switch()
        };

        // when / then
        assert_ne!(sw0, sw1);
    }

    #[test]
    fn eq_returns_false_when_targets_are_different() {
        // given
        let sw0 = gen_switch();
        let other_target = Location::new("different", false, None);
        let sw1 = Switch {
            target: other_target,
            ..gen_switch()
        };

        // when / then
        assert_ne!(sw0, sw1);
    }

    #[test]
    fn eq_returns_false_when_resets_contain_different_clocks() {
        // given
        let sw0 = gen_switch();
        let sw1 = Switch {
            reset: vec![Clock::new("other")],
            ..gen_switch()
        };

        // when / then
        assert_ne!(sw0, sw1);
    }

    #[test]
    fn eq_is_reflexive() {
        // given
        let a = gen_switch();

        // when / then
        assert_eq!(a, a);
    }

    #[test]
    fn eq_is_symmetric() {
        // given
        let a = gen_switch();
        let b = a.clone();

        // when / then
        assert!(!(a == b) || b == a);
    }

    #[test]
    fn eq_is_transitive() {
        // given
        let a = gen_switch();
        let b = a.clone();
        let c = a.clone();

        // when / then
        assert!(!(a == b && b == c) || a == c);
    }

    fn gen_switch() -> Switch {
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");
        let clause = Clause::new(&clock_x, ClockComparator::LEQ, 42);
        let cc = ClockConstraint::new(Box::from([clause]));
        Switch {
            source: Location::new("source", true, None),
            guard: Some(cc),
            action: String::from("action"),
            reset: vec![clock_x, clock_y],
            target: Location::new("target", false, None),
        }
    }
}
