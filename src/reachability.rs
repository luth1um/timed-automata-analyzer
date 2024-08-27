use crate::symbolic_state::difference_bound_matrix::DifferenceBoundMatrix;
use crate::symbolic_state::SymbolicState;
use crate::ta::clock::Clock;
use crate::ta::location::Location;
use crate::ta::TimedAutomaton;
use std::collections::HashSet;

pub fn find_unreachable_locations(ta: &TimedAutomaton) -> Vec<String> {
    // setup
    let mut visited_states: HashSet<SymbolicState> = HashSet::new();
    let mut states_to_process: Vec<SymbolicState> = Vec::new();
    let mut locations_not_visited: HashSet<String> = ta
        .locations()
        .iter()
        .map(|loc| loc.name().clone())
        .collect();

    let mut clocks_sorted: Vec<Clock> = ta.clocks().clone();
    clocks_sorted.sort();

    let init_loc = ta.find_initial_location();
    let k = ta.find_highest_constant_in_any_clause();
    let init_zone = DifferenceBoundMatrix::for_initial_symbolic_state(ta.clocks().len());
    let init_symbolic_state = SymbolicState::new(init_loc.name(), init_zone);

    visited_states.insert(init_symbolic_state.clone());
    states_to_process.push(init_symbolic_state);
    locations_not_visited.remove(init_loc.name());

    // actual reachability analysis
    while !states_to_process.is_empty() && !locations_not_visited.is_empty() {
        let current = match states_to_process.pop() {
            Some(state) => state,
            None => panic!("No symbolic state found even though vec should not be empty"),
        };

        let mut computed_states = next_states_for_switches(&current, ta, &clocks_sorted, k);
        if let Some(loc_state) = next_state_for_same_location(&current, ta, &clocks_sorted) {
            computed_states.push(loc_state);
        }
        for state in computed_states {
            if visited_states.insert(state.clone()) {
                locations_not_visited.remove(state.location());
                states_to_process.push(state);
            }
        }
    }

    // process result for output
    locations_not_visited.iter().cloned().collect()
}

fn next_states_for_switches(
    current_state: &SymbolicState,
    ta: &TimedAutomaton,
    all_clocks_sorted: &Vec<Clock>,
    highest_constant_in_ta: i32,
) -> Vec<SymbolicState> {
    let mut next_states: Vec<SymbolicState> = Vec::new();

    ta.switches()
        .iter()
        .filter(|sw| sw.source().name() == current_state.location())
        .for_each(|sw| {
            let mut next_zone = current_state.zone().clone();
            if let Some(guard) = sw.guard() {
                if next_zone.and(guard, all_clocks_sorted).is_none() {
                    // result unsatisfiable
                    return;
                }
            }
            next_zone.reset(sw.reset(), all_clocks_sorted);
            if let Some(invariant) = sw.target().invariant() {
                if next_zone.and(invariant, all_clocks_sorted).is_none() {
                    // result unsatisfiable
                    return;
                }
            }
            next_zone.k_norm(highest_constant_in_ta);
            let next_state = SymbolicState::new(sw.target().name(), next_zone);
            next_states.push(next_state);
        });

    next_states
}

fn next_state_for_same_location(
    current_state: &SymbolicState,
    ta: &TimedAutomaton,
    all_clocks_sorted: &Vec<Clock>,
) -> Option<SymbolicState> {
    let loc: &Location = match ta
        .locations()
        .iter()
        .find(|loc| (*loc).name() == current_state.location())
    {
        Some(loc) => loc,
        None => panic!(
            "Cannot find location with name {}",
            current_state.location()
        ),
    };

    let mut next_zone = current_state.zone().clone();
    next_zone.up();
    if let Some(invariant) = loc.invariant() {
        next_zone.and(invariant, all_clocks_sorted)?;
    }

    Some(SymbolicState::new(current_state.location(), next_zone))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock_constraint::clause::{Clause, ClockComparator};
    use crate::ta::clock_constraint::ClockConstraint;
    use crate::ta::switch::Switch;

    #[test]
    fn find_unreachable_locations_returns_empty_when_ta_only_has_single_location() {
        // given
        let ta = TimedAutomaton::new(
            Box::from(vec![Location::new("init", true, None)]),
            Box::from(vec![]),
            Box::from(vec![]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_returns_empty_when_ta_only_has_single_location_with_invariant() {
        // given
        let clock = Clock::new("x");
        let clause = Clause::new(&clock, ClockComparator::LEQ, 42);
        let invariant = ClockConstraint::new(Box::from(vec![clause]));
        let ta = TimedAutomaton::new(
            Box::from(vec![Location::new("init", true, Some(invariant))]),
            Box::from(vec![clock]),
            Box::from(vec![]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_returns_empty_when_ta_has_multiple_reachable_locations() {
        // given
        let clock = Clock::new("x");
        let clause = Clause::new(&clock, ClockComparator::LEQ, 42);
        let invariant = ClockConstraint::new(Box::from(vec![clause]));
        let loc0 = Location::new("init", true, Some(invariant.clone()));
        let loc1 = Location::new("other", false, Some(invariant));
        let sw = Switch::new(&loc0, None, "action", Box::from(vec![]), &loc1);
        let ta = TimedAutomaton::new(
            Box::from(vec![loc0, loc1]),
            Box::from(vec![clock]),
            Box::from(vec![sw]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_returns_loc_when_loc_is_unreachable_due_to_constraints() {
        // given
        let clock = Clock::new("x");

        let clause_leq42 = Clause::new(&clock, ClockComparator::LEQ, 42);
        let invariant = ClockConstraint::new(Box::from(vec![clause_leq42]));

        let clause_g42 = Clause::new(&clock, ClockComparator::GREATER, 42);
        let guard = ClockConstraint::new(Box::from(vec![clause_g42]));

        let loc0 = Location::new("init", true, None);
        let loc1 = Location::new("other", false, Some(invariant));
        let sw = Switch::new(&loc0, Some(guard), "action", Box::from(vec![]), &loc1);
        let ta = TimedAutomaton::new(
            Box::from(vec![loc0, loc1.clone()]),
            Box::from(vec![clock]),
            Box::from(vec![sw]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert_eq!(result.len(), 1);
        assert_eq!(result.first(), Some(loc1.name()));
    }

    #[test]
    fn find_unreachable_locations_marks_loc_as_reachable_when_only_reachable_with_reset() {
        // given
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");

        let clause_x_g42 = Clause::new(&clock_x, ClockComparator::GREATER, 42);
        let guard0 = ClockConstraint::new(Box::from(vec![clause_x_g42]));

        let clause_y_leq42 = Clause::new(&clock_y, ClockComparator::LEQ, 42);
        let guard1 = ClockConstraint::new(Box::from(vec![clause_y_leq42]));

        let loc0 = Location::new("loc0", true, None);
        let loc1 = Location::new("loc1", false, None);
        let loc2 = Location::new("loc2", false, None);

        let sw0 = Switch::new(
            &loc0,
            Some(guard0),
            "a0",
            Box::from(vec![clock_y.clone()]),
            &loc1,
        );
        let sw1 = Switch::new(&loc1, Some(guard1), "a1", Box::from(vec![]), &loc2);

        let ta = TimedAutomaton::new(
            Box::from(vec![loc0, loc1, loc2]),
            Box::from(vec![clock_x, clock_y]),
            Box::from(vec![sw0, sw1]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_terminates_when_k_normalization_is_necessary() {
        // given
        // (Fig. 4 from "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi)
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");

        let clause_x_leq10 = Clause::new(&clock_x, ClockComparator::LEQ, 10);
        let invariant_loop = ClockConstraint::new(Box::from(vec![clause_x_leq10.clone()]));

        let clause_x_geq10 = Clause::new(&clock_x, ClockComparator::GEQ, 10);
        let guard_ll = ClockConstraint::new(Box::from(vec![clause_x_leq10, clause_x_geq10]));

        let clause_y_geq20 = Clause::new(&clock_y, ClockComparator::GEQ, 20);
        let guard_le = ClockConstraint::new(Box::from(vec![clause_y_geq20]));

        let loc_start = Location::new("start", true, None);
        let loc_loop = Location::new("loop", false, Some(invariant_loop));
        let loc_end = Location::new("end", false, None);

        let sw_sl = Switch::new(
            &loc_start,
            None,
            "sl",
            Box::from(vec![clock_x.clone(), clock_y.clone()]),
            &loc_loop,
        );
        let sw_ll = Switch::new(
            &loc_loop,
            Some(guard_ll),
            "ll",
            Box::from(vec![clock_x.clone()]),
            &loc_loop,
        );
        let sw_le = Switch::new(
            &loc_loop,
            Some(guard_le),
            "le",
            Box::from(vec![clock_x.clone(), clock_y.clone()]),
            &loc_end,
        );

        let ta = TimedAutomaton::new(
            Box::from(vec![loc_start, loc_loop, loc_end]),
            Box::from(vec![clock_x, clock_y]),
            Box::from(vec![sw_sl, sw_ll, sw_le]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_terminates_when_k_norm_is_necessary_minimal_example() {
        // given
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");

        let clause_x_leq10 = Clause::new(&clock_x, ClockComparator::LEQ, 10);
        let invariant_loop = ClockConstraint::new(Box::from(vec![clause_x_leq10.clone()]));

        let clause_x_geq10 = Clause::new(&clock_x, ClockComparator::GEQ, 10);
        let guard_ll = ClockConstraint::new(Box::from(vec![clause_x_leq10, clause_x_geq10]));

        let clause_x_g20 = Clause::new(&clock_x, ClockComparator::GREATER, 20);
        let guard_le = ClockConstraint::new(Box::from(vec![clause_x_g20]));

        let loc_loop = Location::new("loop", true, Some(invariant_loop));
        let loc_end = Location::new("end", false, None);

        let sw_ll = Switch::new(
            &loc_loop,
            Some(guard_ll),
            "ll",
            Box::from(vec![clock_x.clone()]),
            &loc_loop,
        );
        let sw_le = Switch::new(
            &loc_loop,
            Some(guard_le),
            "le",
            Box::from(vec![clock_x.clone(), clock_y.clone()]),
            &loc_end,
        );

        let ta = TimedAutomaton::new(
            Box::from(vec![loc_loop, loc_end.clone()]),
            Box::from(vec![clock_x, clock_y]),
            Box::from(vec![sw_ll, sw_le]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert_eq!(result.len(), 1);
        assert_eq!(result.first(), Some(loc_end.name()));
    }

    #[test]
    fn find_unreachable_locations_works_correctly_when_ta_has_no_constraints_and_no_clocks() {
        // given
        let loc_start = Location::new("start", true, None);
        let loc_loop = Location::new("loop", false, None);
        let loc_end = Location::new("end", false, None);

        let sw_sl = Switch::new(&loc_start, None, "sl", Box::from(vec![]), &loc_loop);
        let sw_ll = Switch::new(&loc_loop, None, "ll", Box::from(vec![]), &loc_loop);
        let sw_le = Switch::new(&loc_loop, None, "le", Box::from(vec![]), &loc_end);

        let ta = TimedAutomaton::new(
            Box::from(vec![loc_start, loc_loop, loc_end]),
            Box::from(vec![]),
            Box::from(vec![sw_sl, sw_ll, sw_le]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert!(result.is_empty());
    }

    #[test]
    fn find_unreachable_locations_returns_non_initial_locs_when_ta_has_no_switches() {
        // given
        let init = Location::new("init", true, None);
        let other = Location::new("other", false, None);
        let ta = TimedAutomaton::new(
            Box::from(vec![init, other.clone()]),
            Box::from(vec![]),
            Box::from(vec![]),
        );

        // when
        let result = find_unreachable_locations(&ta);

        // then
        assert_eq!(result.len(), 1);
        assert_eq!(result.first(), Some(other.name()));
    }

    #[test]
    fn next_states_for_switches_returns_all_states_when_all_states_satisfiable() {
        // given
        let k = 42;
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::LEQ, k);
        let cc = ClockConstraint::new(Box::from(vec![clause]));

        let init = Location::new("init", true, None);
        let other = Location::new("other", false, None);
        let another = Location::new("another", false, None);

        let sw_io = Switch::new(&init, Some(cc.clone()), "io", Box::from(vec![]), &other);
        let sw_ia = Switch::new(&init, Some(cc.clone()), "ia", Box::from(vec![]), &another);

        let ta = TimedAutomaton::new(
            Box::from(vec![init.clone(), other.clone(), another.clone()]),
            Box::from(clocks.clone()),
            Box::from(vec![sw_io, sw_ia]),
        );

        let mut zone = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        zone.up();
        let state = SymbolicState::new(init.name(), zone);

        let mut expected_zone = state.zone().clone();
        expected_zone.and(&cc, &clocks);
        let state_other = SymbolicState::new(other.name(), expected_zone.clone());
        let state_another = SymbolicState::new(another.name(), expected_zone);
        let expected_states = vec![state_other, state_another];

        // when
        let result = next_states_for_switches(&state, &ta, &clocks, k as i32);

        // then
        assert_eq!(result, expected_states);
    }

    #[test]
    fn next_states_for_switches_returns_empty_vec_when_loc_has_no_outgoing_switches() {
        // given
        let k = 0;
        let clocks: Vec<Clock> = vec![];

        let init = Location::new("init", true, None);
        let other = Location::new("other", false, None);
        let another = Location::new("another", false, None);

        // switches are only incoming to init! no outgoing switches from init
        let sw_oi = Switch::new(&other, None, "oi", Box::from(vec![]), &init);
        let sw_ai = Switch::new(&another, None, "ai", Box::from(vec![]), &init);

        let ta = TimedAutomaton::new(
            Box::from(vec![init.clone(), other, another]),
            Box::from(vec![]),
            Box::from(vec![sw_oi, sw_ai]),
        );

        let mut zone = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        zone.up();
        let state = SymbolicState::new(init.name(), zone);

        // when
        let result = next_states_for_switches(&state, &ta, &clocks, k);

        // then
        assert_eq!(result, vec![]);
    }

    #[test]
    fn next_states_for_switches_returns_only_reachable_states_when_some_states_are_unsatisfiable() {
        // given
        let k = 42;
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause_leq_k = Clause::new(&clock, ClockComparator::LEQ, k);
        let clause_greater_k = Clause::new(&clock, ClockComparator::GREATER, k);
        let cc_satisfiable = ClockConstraint::new(Box::from(vec![clause_leq_k.clone()]));
        let cc_unsatisfiable =
            ClockConstraint::new(Box::from(vec![clause_leq_k.clone(), clause_greater_k]));

        let init = Location::new("init", true, None);
        let reachable = Location::new("reachable", false, None);
        let unreachable = Location::new("unreachable", false, None);

        let sw_sat = Switch::new(
            &init,
            Some(cc_satisfiable.clone()),
            "sat",
            Box::from(vec![]),
            &reachable,
        );
        let sw_unsat = Switch::new(
            &init,
            Some(cc_unsatisfiable),
            "unsat",
            Box::from(vec![]),
            &unreachable,
        );

        let ta = TimedAutomaton::new(
            Box::from(vec![init.clone(), reachable.clone(), unreachable]),
            Box::from(clocks.clone()),
            Box::from(vec![sw_sat, sw_unsat]),
        );

        let mut zone = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        zone.up();
        let state = SymbolicState::new(init.name(), zone);

        let mut expected_zone = state.zone().clone();
        expected_zone.and(&cc_satisfiable, &clocks);
        let state_other = SymbolicState::new(reachable.name(), expected_zone);
        let expected_states = vec![state_other];

        // when
        let result = next_states_for_switches(&state, &ta, &clocks, k as i32);

        // then
        assert_eq!(result, expected_states);
    }

    #[test]
    fn next_state_for_same_location_has_correct_result_when_location_does_not_have_invariant() {
        // given
        let loc = Location::new("init", true, None);
        let clocks: Vec<Clock> = vec![Clock::new("x")];
        let ta = TimedAutomaton::new(
            Box::from(vec![loc.clone()]),
            Box::from(clocks.clone()),
            Box::from(vec![]),
        );

        let zone = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        let state = SymbolicState::new(loc.name(), zone.clone());

        let mut expected_zone = zone.clone();
        expected_zone.up();
        let expected_state = SymbolicState::new(loc.name(), expected_zone);

        // when
        let result = next_state_for_same_location(&state, &ta, &clocks);

        // then
        assert_eq!(result, Some(expected_state));
    }

    #[test]
    fn next_state_for_same_location_has_correct_result_when_location_has_invariant() {
        // given
        let k = 42;
        let clock = Clock::new("x");
        let clocks: Vec<Clock> = vec![clock.clone()];

        let clause = Clause::new(&clock, ClockComparator::LEQ, k);
        let invariant = ClockConstraint::new(Box::from(vec![clause]));

        let loc = Location::new("init", true, Some(invariant.clone()));
        let ta = TimedAutomaton::new(
            Box::from(vec![loc.clone()]),
            Box::from(clocks.clone()),
            Box::from(vec![]),
        );

        let zone = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        let state = SymbolicState::new(loc.name(), zone.clone());

        let mut expected_zone = zone.clone();
        expected_zone.up();
        expected_zone.and(&invariant, &clocks);
        let expected_state = SymbolicState::new(loc.name(), expected_zone);

        // when
        let result = next_state_for_same_location(&state, &ta, &clocks);

        // then
        assert_eq!(result, Some(expected_state));
    }
}
