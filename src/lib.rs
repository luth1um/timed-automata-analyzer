use crate::ta::TimedAutomaton;
use crate::validation::validate_input_ta;
use wasm_bindgen::prelude::*;

mod reachability;
mod symbolic_state;
pub mod ta;
mod util;
mod validation;

#[wasm_bindgen(js_name = findUnreachableLocations)]
pub fn find_unreachable_locations(ta: TimedAutomaton) -> Vec<String> {
    panic!("test");

    if let Err(msgs) = validate_input_ta(&ta) {
        wasm_bindgen::throw_str(&format!(
            "The input TA failed some validation checks: {}",
            msgs.join(" ")
        ));
    }

    reachability::find_unreachable_locations(&ta)
}
