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

    /// Finds the initial location of the TA. Please be aware that the initial location is not
    /// explicitly stored, such that calling this method repeatedly would cause computations for
    /// every call.
    ///
    /// # Panics
    /// This method panics if the number of initial locations of the TA is not exactly 1.
    pub fn find_initial_location(&self) -> &Location {
        let marked_init: Vec<&Location> = self
            .locations()
            .iter()
            .filter(|loc| (*loc).is_initial())
            .collect();
        if marked_init.len() > 1 {
            panic!(
                "Found multiple initial locations {:?} although there should only be 1",
                marked_init
            );
        }
        match marked_init.first() {
            Some(loc) => *loc,
            None => panic!(
                "Did not find any initial location in {:?}",
                self.locations()
            ),
        }
    }

    /// Finds the highest constant used in any clock constraint of the TA. This constant is required
    /// for k-normalization. Please be aware that the highest constant is not explicitly stored,
    /// such that calling this method repeatedly would cause computations for every call.
    ///
    /// If the TA does not contain any clock constraint, this method returns `0`.
    pub fn find_highest_constant_in_any_clause(&self) -> i32 {
        let invariants = self
            .locations
            .iter()
            .map(|loc| loc.invariant())
            .filter_map(|cc| cc.clone());
        let guards = self
            .switches
            .iter()
            .map(|sw| sw.guard())
            .filter_map(|cc| cc.clone());

        let mut all_constants: Vec<u32> = invariants
            .chain(guards)
            .map(|cc| cc.clauses().clone())
            .flat_map(|clauses| clauses)
            .map(|clause| clause.rhs())
            .collect();
        all_constants.sort_unstable();

        match all_constants.last() {
            Some(k) => *k as i32,
            None => 0,
        }
        // TODO: write tests
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
    fn find_initial_location_returns_initial_location_when_called_on_ta_with_single_init_loc() {
        // given
        let init_loc = gen_loc_source();
        let ta = TimedAutomaton::new(
            Box::from(vec![init_loc.clone(), gen_loc_target()]),
            Box::from(gen_clocks()),
            Box::from(vec![gen_switch()]),
        );

        // when
        let result = ta.find_initial_location();

        // then
        assert_eq!(*result, init_loc);
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
