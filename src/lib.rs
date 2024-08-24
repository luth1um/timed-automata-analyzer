use crate::ta::TimedAutomaton;
use crate::validation::validate_input_ta;
use wasm_bindgen::prelude::*;

mod difference_bound_matrix;
pub mod ta;
mod util;
mod validation;

#[wasm_bindgen(js_name = findUnreachableLocations)]
pub fn find_unreachable_locations(ta: TimedAutomaton) -> Vec<String> {
    if let Err(msgs) = validate_input_ta(&ta) {
        wasm_bindgen::throw_str(&format!(
            "The input TA failed some validation checks: {}",
            msgs.join(" ")
        ));
    }

    // TODO: replace remainder of this function by actual reachability analysis
    let mut result: Vec<String> = Vec::new();

    for loc in ta.locations() {
        result.push(loc.name().clone());
    }

    for clock in ta.clocks() {
        result.push(clock.name().clone());
    }

    for sw in ta.switches() {
        result.push(sw.action().clone());
    }

    result
}
