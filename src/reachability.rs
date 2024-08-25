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
    while !states_to_process.is_empty() {
        let current = match states_to_process.pop() {
            Some(state) => state,
            None => panic!("No symbolic state found even though vec is not empty"),
        };

        let mut computed_states = next_states_for_switches(&current, &ta, &clocks_sorted, k);
        if let Some(loc_state) = next_state_for_same_location(&current, &ta, &clocks_sorted, k) {
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
    locations_not_visited
        .iter()
        .map(|name| name.clone())
        .collect()
    // TODO: write tests
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
                if let None = next_zone.and(guard, all_clocks_sorted) {
                    // result unsatisfiable
                    return;
                }
            }
            next_zone.reset(sw.reset(), all_clocks_sorted);
            if let Some(invariant) = sw.target().invariant() {
                if let None = next_zone.and(invariant, all_clocks_sorted) {
                    // result unsatisfiable
                    return;
                }
            }
            next_zone.k_norm(highest_constant_in_ta);
            let next_state = SymbolicState::new(sw.target().name(), next_zone);
            next_states.push(next_state);
        });

    next_states
    // TODO: write tests
}

fn next_state_for_same_location(
    current_state: &SymbolicState,
    ta: &TimedAutomaton,
    all_clocks_sorted: &Vec<Clock>,
    highest_constant_in_ta: i32,
) -> Option<SymbolicState> {
    let loc: &Location = match ta
        .locations()
        .iter()
        .filter(|loc| (*loc).name() == current_state.location())
        .next()
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
        next_zone.and(&invariant, &all_clocks_sorted)?;
    }
    next_zone.k_norm(highest_constant_in_ta);

    Some(SymbolicState::new(current_state.location(), next_zone))
    // TODO: write tests
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
}
