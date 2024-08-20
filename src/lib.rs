use wasm_bindgen::prelude::*;

#[wasm_bindgen(js_name = findUnreachableLocations)]
pub fn find_unreachable_locations(ta: TimedAutomaton) -> Vec<String> {
    let mut result = Vec::new();
    result.push(ta.name);
    result
}

#[wasm_bindgen]
pub struct TimedAutomaton {
    name: String,
}

#[wasm_bindgen]
impl TimedAutomaton {
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str) -> Self {
        TimedAutomaton {
            name: String::from(name),
        }
    }
}
