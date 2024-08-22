use crate::ta::TimedAutomaton;

pub fn validate_input_ta(ta: &TimedAutomaton) -> Result<(), String> {
    // TODO: add more input validations and write tests for validations
    // - contains no locations
    // - all clocks used in invariants and guards are contained in set of clocks
    // - all locations used in guards (source and target) are contained in set of locations
    // - set of clock does not contain a clock name twice
    // - set of locations does not contain a location name twice
    // - invariant of initial location does not have lower bound (e.g., x > 2)

    // TODO: can validation functions be stored in vec to have elegant for-each loop?

    let mut error_msgs: Vec<String> = Vec::new();

    if let Err(err_msg) = validate_init_loc_count(ta) {
        error_msgs.push(format!("{err_msg}"));
    }

    if error_msgs.is_empty() {
        return Ok(());
    }
    Err(error_msgs.join(" "))
}

fn validate_init_loc_count(ta: &TimedAutomaton) -> Result<(), String> {
    let init_loc_count = ta
        .locations()
        .iter()
        .filter(|loc| (*loc).is_initial())
        .count();
    if init_loc_count == 0 {
        return Err(String::from("The TA does not have an initial location.").into());
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
        assert_eq!(result.unwrap(), ());
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
            Err(msg) => assert_eq!(msg, "The TA does not have an initial location."),
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
            Err(msg) => assert_eq!(
                msg,
                format!(
                    "The TA has multiple initial locations ({}, {}).",
                    init0.name(),
                    init1.name()
                )
            ),
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
