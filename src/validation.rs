use crate::ta::clock_constraint::clause::ClockComparator;
use crate::ta::clock_constraint::clause::ClockComparator::LESSER;
use crate::ta::TimedAutomaton;
use std::collections::HashMap;

type ValidationFnResult = Result<(), String>;
type ValidationFn = fn(&TimedAutomaton) -> ValidationFnResult;

/// The highest allowed constant is validated as the type for the rhs in clauses is `u32`. However,
/// for analysis we need `i32`. Additionally, we need one bit for the encoding of DBM entries and
/// another bit to accommodate for temporary values before k-normalization.
const MAX_ALLOWED_CONSTANT_IN_TA: i32 = (i32::MAX >> 2) - 2;

pub fn validate_input_ta(ta: &TimedAutomaton) -> Result<(), Vec<String>> {
    // TODO: add more input validations and write tests for validations
    // - all clocks used in invariants and guards are contained in set of clocks
    // - all locations used in guards (source and target) are contained in set of locations

    let mut error_msgs: Vec<String> = Vec::new();
    let validation_fns: Vec<ValidationFn> = vec![
        validate_init_loc_count,
        validate_at_least_one_loc,
        validate_all_invariants_downward_closed,
        validate_highest_constant,
        validate_unique_location_names,
        validate_unique_clock_names,
    ];

    for validation_fn in validation_fns {
        if let Err(err_msg) = validation_fn(ta) {
            error_msgs.push(err_msg);
        }
    }

    if error_msgs.is_empty() {
        return Ok(());
    }
    Err(error_msgs)
}

fn validate_init_loc_count(ta: &TimedAutomaton) -> ValidationFnResult {
    let init_loc_count = ta
        .locations()
        .iter()
        .filter(|loc| (*loc).is_initial())
        .count();
    if init_loc_count == 0 {
        return Err(String::from("The TA does not have an initial location."));
    }
    if init_loc_count > 1 {
        let init_loc_names: Vec<String> = ta
            .locations()
            .iter()
            .filter(|loc| (*loc).is_initial())
            .map(|loc| loc.name().clone())
            .collect();
        return Err(format!(
            "The TA has multiple initial locations ({}).",
            init_loc_names.join(", ")
        ));
    }
    Ok(())
}

fn validate_at_least_one_loc(ta: &TimedAutomaton) -> ValidationFnResult {
    if ta.locations().is_empty() {
        return Err(String::from("The TA does not have any locations."));
    }
    Ok(())
}

fn validate_all_invariants_downward_closed(ta: &TimedAutomaton) -> ValidationFnResult {
    let mut violating_locs = Vec::new();

    'outer: for location in ta.locations() {
        if let Some(invariant) = location.invariant() {
            for clause in invariant.clauses() {
                if clause.op() != ClockComparator::LEQ && clause.op() != LESSER {
                    violating_locs.push(location.name().clone());
                    continue 'outer;
                }
            }
        }
    }

    if violating_locs.is_empty() {
        return Ok(());
    }
    Err(format!(
        "The invariants of some locations are not downward closed: {}.",
        violating_locs.join(", ")
    ))
}

fn validate_highest_constant(ta: &TimedAutomaton) -> ValidationFnResult {
    let k = ta.find_highest_constant_in_any_clause();
    if k <= MAX_ALLOWED_CONSTANT_IN_TA {
        return Ok(());
    }
    Err(format!(
        "Highest allowed constant for right-hand side of clauses is {}.",
        MAX_ALLOWED_CONSTANT_IN_TA
    ))
}

fn validate_unique_location_names(ta: &TimedAutomaton) -> ValidationFnResult {
    let mut name_count = HashMap::new();
    for location in ta.locations() {
        let count = name_count.entry(location.name()).or_insert(0);
        *count += 1;
    }

    let mut duplicate_names = Vec::new();
    for (loc_name, count) in name_count {
        if count > 1 {
            duplicate_names.push(loc_name.clone());
        }
    }

    if duplicate_names.is_empty() {
        return Ok(());
    }
    Err(format!(
        "Some location names are not unique: {}.",
        duplicate_names.join(", ")
    ))
}

fn validate_unique_clock_names(ta: &TimedAutomaton) -> ValidationFnResult {
    let mut name_count = HashMap::new();
    for clock in ta.clocks() {
        let count = name_count.entry(clock.name()).or_insert(0);
        *count += 1;
    }

    let mut duplicate_names = Vec::new();
    for (clock_name, count) in name_count {
        if count > 1 {
            duplicate_names.push(clock_name.clone());
        }
    }

    if duplicate_names.is_empty() {
        return Ok(());
    }
    Err(format!(
        "Some clock names are not unique: {}.",
        duplicate_names.join(", ")
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock::Clock;
    use crate::ta::clock_constraint::clause::{Clause, ClockComparator};
    use crate::ta::clock_constraint::ClockConstraint;
    use crate::ta::location::Location;
    use crate::ta::switch::Switch;

    #[test]
    fn validate_input_ta_returns_ok_when_ta_is_valid() {
        // given
        let ta = gen_ta();

        // when
        let result = validate_input_ta(&ta);

        // then
        assert!(result.is_ok());
    }

    #[test]
    fn validate_input_ta_returns_err_when_ta_does_not_have_initial_location() {
        // given
        let ta = TimedAutomaton::new(
            Box::from(vec![gen_loc_target()]),
            Box::from(gen_clocks()),
            Box::from(Vec::new()),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&String::from("The TA does not have an initial location.")))
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_ta_has_multiple_initial_locations() {
        // given
        let init0 = Location::new("first", true, None);
        let init1 = Location::new("second", true, None);
        let ta = TimedAutomaton::new(
            Box::from(vec![init0.clone(), init1.clone()]),
            Box::from(gen_clocks()),
            Box::from(Vec::new()),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => assert!(msgs.contains(&format!(
                "The TA has multiple initial locations ({}, {}).",
                init0.name(),
                init1.name()
            ))),
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_ta_does_not_have_any_locations() {
        // given
        let ta = TimedAutomaton::new(
            Box::from(Vec::new()),
            Box::from(gen_clocks()),
            Box::from(Vec::new()),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&String::from("The TA does not have any locations.")))
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_invariants_not_downward_closed() {
        // given
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];

        let clause_not_dw_closed = Clause::new(&clock, ClockComparator::GREATER, 42);
        let cc_not_dw_closed = ClockConstraint::new(Box::from(vec![clause_not_dw_closed]));
        let clause_dw_closed = Clause::new(&clock, ClockComparator::LEQ, 42);
        let cc_dw_closed = ClockConstraint::new(Box::from(vec![clause_dw_closed]));

        let loc0 = Location::new("zero", true, Some(cc_not_dw_closed.clone()));
        let loc1 = Location::new("one", false, Some(cc_dw_closed));
        let loc2 = Location::new("two", false, None);
        let loc3 = Location::new("three", false, Some(cc_not_dw_closed));

        let ta = TimedAutomaton::new(
            Box::from(vec![loc0.clone(), loc1, loc2, loc3.clone()]),
            Box::from(clocks),
            Box::from(vec![]),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&String::from(&format!(
                    "The invariants of some locations are not downward closed: {}, {}.",
                    loc0.name(),
                    loc3.name()
                ))));
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_highest_used_k_in_ta_is_greater_than_allowed() {
        // given
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];

        let clause = Clause::new(
            &clock,
            ClockComparator::LEQ,
            MAX_ALLOWED_CONSTANT_IN_TA as u32 + 1,
        );
        let cc = ClockConstraint::new(Box::from(vec![clause]));

        let loc = Location::new("zero", true, Some(cc));

        let ta = TimedAutomaton::new(Box::from(vec![loc]), Box::from(clocks), Box::from(vec![]));

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&format!(
                    "Highest allowed constant for right-hand side of clauses is {}.",
                    MAX_ALLOWED_CONSTANT_IN_TA
                )))
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_location_names_are_not_unique() {
        // given
        let dupl_0 = Location::new("duplicate", true, None);
        let dupl_1 = Location::new("duplicate", false, None);
        let unique = Location::new("unique", false, None);
        let ta = TimedAutomaton::new(
            Box::from(vec![dupl_0.clone(), dupl_1, unique]),
            Box::from(vec![]),
            Box::from(vec![]),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&format!(
                    "Some location names are not unique: {}.",
                    dupl_0.name()
                )))
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    #[test]
    fn validate_input_ta_returns_err_when_clock_names_are_not_unique() {
        // given
        let dupl_0 = Clock::new("duplicate");
        let dupl_1 = Clock::new("duplicate");
        let unique = Clock::new("unique");
        let ta = TimedAutomaton::new(
            Box::from(vec![]),
            Box::from(vec![dupl_0.clone(), dupl_1, unique]),
            Box::from(vec![]),
        );

        // when
        let result = validate_input_ta(&ta);

        // then
        match result {
            Err(msgs) => {
                assert!(msgs.contains(&format!(
                    "Some clock names are not unique: {}.",
                    dupl_0.name()
                )))
            }
            _ => panic!("Expected an Err, got an Ok"),
        }
    }

    fn gen_clocks() -> Vec<Clock> {
        vec![Clock::new("c0"), Clock::new("c1")]
    }

    fn gen_loc_source() -> Location {
        Location::new("init", true, None)
    }

    fn gen_loc_target() -> Location {
        Location::new("other", false, None)
    }

    fn gen_switch() -> Switch {
        let clock0 = Clock::new("c0");
        let clause = Clause::new(&clock0, ClockComparator::GREATER, 420);
        let cc = ClockConstraint::new(Box::from([clause]));
        Switch::new(
            &gen_loc_source(),
            Some(cc),
            "hi",
            Box::from(gen_clocks()),
            &gen_loc_target(),
        )
    }

    fn gen_ta() -> TimedAutomaton {
        TimedAutomaton::new(
            Box::from(vec![gen_loc_source(), gen_loc_target()]),
            Box::from(gen_clocks()),
            Box::from(vec![gen_switch()]),
        )
    }
}
