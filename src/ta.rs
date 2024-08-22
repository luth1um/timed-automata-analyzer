use crate::ta::clock::Clock;
use crate::ta::location::Location;
use crate::ta::switch::Switch;
use crate::util::vecs_eq_without_order;
use wasm_bindgen::prelude::wasm_bindgen;

pub mod clock;
pub mod clock_constraint;
pub mod location;
pub mod switch;

#[wasm_bindgen]
#[derive(Debug, Clone, Eq)]
pub struct TimedAutomaton {
    locations: Vec<Location>,
    clocks: Vec<Clock>,
    switches: Vec<Switch>,
}

#[wasm_bindgen]
impl TimedAutomaton {
    #[wasm_bindgen(constructor)]
    pub fn new(locations: Box<[Location]>, clocks: Box<[Clock]>, switches: Box<[Switch]>) -> Self {
        Self {
            locations: Vec::from(locations),
            clocks: Vec::from(clocks),
            switches: Vec::from(switches),
        }
    }
}

impl TimedAutomaton {
    pub fn locations(&self) -> &Vec<Location> {
        &self.locations
    }

    pub fn clocks(&self) -> &Vec<Clock> {
        &self.clocks
    }

    pub fn switches(&self) -> &Vec<Switch> {
        &self.switches
    }
}

impl PartialEq<Self> for TimedAutomaton {
    fn eq(&self, other: &Self) -> bool {
        vecs_eq_without_order(&self.clocks, &other.clocks)
            && vecs_eq_without_order(&self.locations, &other.locations)
            && vecs_eq_without_order(&self.switches, &other.switches)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock_constraint::clause::{Clause, ClockComparator};
    use crate::ta::clock_constraint::ClockConstraint;

    #[test]
    fn new_returns_correct_ta_when_called() {
        // given
        let locs = vec![gen_loc_source(), gen_loc_target()];
        let clocks = gen_clocks();
        let switches = vec![gen_switch()];

        // when
        let result = TimedAutomaton::new(
            Box::from(locs.clone()),
            Box::from(clocks.clone()),
            Box::from(switches.clone()),
        );

        // then
        assert_eq!(result.locations, locs);
        assert_eq!(result.clocks, clocks);
        assert_eq!(result.switches, switches);
    }

    #[test]
    fn eq_returns_true_when_ta_are_eq() {
        // given
        let ta0 = gen_ta();
        let ta1 = gen_ta();

        // when / then
        assert_eq!(ta0, ta1);
    }

    #[test]
    fn eq_returns_false_when_locations_are_different() {
        // given
        let ta0 = gen_ta();
        let ta1 = TimedAutomaton {
            locations: vec![gen_loc_source()],
            ..ta0.clone()
        };

        // when / then
        assert_ne!(ta0, ta1);
    }

    #[test]
    fn eq_returns_false_when_clocks_are_different() {
        // given
        let ta0 = gen_ta();
        let ta1 = TimedAutomaton {
            clocks: vec![Clock::new("different")],
            ..ta0.clone()
        };

        // when / then
        assert_ne!(ta0, ta1);
    }

    #[test]
    fn eq_returns_false_when_switches_are_different() {
        // given
        let ta0 = gen_ta();

        let clock_x = Clock::new("other");
        let clause = Clause::new(&clock_x, ClockComparator::GEQ, 876);
        let cc = ClockConstraint::new(Box::from([clause]));
        let other_switch = Switch::new(
            &gen_loc_source(),
            Some(cc),
            "action",
            Box::from(gen_clocks()),
            &gen_loc_target(),
        );
        let ta1 = TimedAutomaton {
            switches: vec![other_switch],
            ..ta0.clone()
        };

        // when / then
        assert_ne!(ta0, ta1);
    }

    #[test]
    fn eq_is_reflexive() {
        // given
        let a = gen_ta();

        // when / then
        assert_eq!(a, a);
    }

    #[test]
    fn eq_is_symmetric() {
        // given
        let a = gen_ta();
        let b = a.clone();

        // when / then
        assert!(!(a == b) || b == a);
    }

    #[test]
    fn eq_is_transitive() {
        // given
        let a = gen_ta();
        let b = a.clone();
        let c = a.clone();

        // when / then
        assert!(!(a == b && b == c) || a == c);
    }

    fn gen_clocks() -> Vec<Clock> {
        vec![Clock::new("x"), Clock::new("y")]
    }

    fn gen_loc_source() -> Location {
        Location::new("source", true, None)
    }

    fn gen_loc_target() -> Location {
        Location::new("target", false, None)
    }

    fn gen_switch() -> Switch {
        let clock_x = Clock::new("x");
        let clause = Clause::new(&clock_x, ClockComparator::LEQ, 42);
        let cc = ClockConstraint::new(Box::from([clause]));
        Switch::new(
            &gen_loc_source(),
            Some(cc),
            "action",
            Box::from(gen_clocks()),
            &gen_loc_target(),
        )
    }

    fn gen_ta() -> TimedAutomaton {
        TimedAutomaton {
            locations: vec![gen_loc_source(), gen_loc_target()],
            clocks: gen_clocks(),
            switches: vec![gen_switch()],
        }
    }
}
