use crate::symbolic_state::difference_bound_matrix::DifferenceBoundMatrix;
use crate::symbolic_state::SymbolicState;
use crate::ta::clock::Clock;
use crate::ta::location::Location;
use crate::ta::TimedAutomaton;
use std::collections::HashSet;
use std::iter;

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

        let guard_states = next_states_for_switches(&current, &ta, &clocks_sorted, k);
        let loc_state = next_state_for_same_location(&current, &ta, &clocks_sorted, k);

        for state in iter::once(loc_state).chain(guard_states) {
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
                next_zone.and(guard, all_clocks_sorted);
            }
            next_zone.reset(sw.reset(), all_clocks_sorted);
            if let Some(invariant) = sw.target().invariant() {
                next_zone.and(invariant, all_clocks_sorted);
            }
            next_zone.k_norm(highest_constant_in_ta);
            let next_state = SymbolicState::new(current_state.location(), next_zone);
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
) -> SymbolicState {
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
        next_zone.and(&invariant, &all_clocks_sorted);
    }
    next_zone.k_norm(highest_constant_in_ta);

    SymbolicState::new(current_state.location(), next_zone)
    // TODO: write tests
}
