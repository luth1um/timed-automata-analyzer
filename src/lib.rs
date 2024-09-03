use crate::ta::TimedAutomaton;
use crate::validation::validate_input_ta;
use wasm_bindgen::prelude::*;

mod reachability;
mod symbolic_state;
pub mod ta;
mod util;
mod validation;

/// Checks all locations of the input TA for reachability and returns all unreachable locations. The
/// result will be empty if all locations are reachable.
///
/// This function will throw an error if one or more validation checks fail. The following
/// properties will be validated:
/// <ul>
/// <li>There exists exactly one initial location.</li>
/// <li>The set of locations is non-empty.</li>
/// <li>All invariants are downward-closed.</li>
/// <li>The highest constant used in any clock constraint is not greater than the highest allowed
/// value (536870909).</li>
/// <li>All locations names are unique.</li>
/// <li>All clock names are unique.</li>
/// <li>All clocks used in clock constraints are also contained in the set of clocks.</li>
/// <li>All location names used as source and target of switches are also contained in the set of
/// locations.</li>
/// </ul>
#[wasm_bindgen(js_name = findUnreachableLocations)]
pub fn find_unreachable_locations(ta: TimedAutomaton) -> Vec<String> {
    if let Err(msgs) = validate_input_ta(&ta) {
        wasm_bindgen::throw_str(&format!(
            "The input TA failed some validation checks. {}",
            msgs.join(" ")
        ));
    }

    reachability::find_unreachable_locations(&ta)
}
