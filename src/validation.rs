use crate::ta::TimedAutomaton;

type ValidationFnResult = Result<(), String>;
type ValidationFn = fn(&TimedAutomaton) -> ValidationFnResult;

pub fn validate_input_ta(ta: &TimedAutomaton) -> Result<(), Vec<String>> {
    // TODO: add more input validations and write tests for validations
    // - all clocks used in invariants and guards are contained in set of clocks
    // - all locations used in guards (source and target) are contained in set of locations
    // - set of clocks does not contain a clock name twice
    // - set of locations does not contain a location name twice
    // - invariants of all locations are downward closed
    // - greatest constant k in TA is <= ((i32::MAX >> 1) - 2), as we use i32 for analysis, and we
    //   need an additional bit for the encoding of DBM entries

    let mut error_msgs: Vec<String> = Vec::new();
    let validation_fns: Vec<ValidationFn> =
        vec![validate_init_loc_count, validate_at_least_one_loc];

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
