use std::fmt;
use std::fmt::{Display, Formatter};
use wasm_bindgen::prelude::wasm_bindgen;

#[wasm_bindgen]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Clock {
    name: String,
}

#[wasm_bindgen]
impl Clock {
    #[wasm_bindgen(constructor)]
    pub fn new(name: &str) -> Self {
        Self {
            name: String::from(name),
        }
    }
}

impl Clock {
    pub fn name(&self) -> &String {
        &self.name
    }
}

impl Display for Clock {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_returns_clock_with_name_when_called() {
        // given
        let name = "x";

        // when
        let clock = Clock::new(name);

        // then
        assert_eq!(clock.name, name);
    }
}
