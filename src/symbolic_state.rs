use crate::symbolic_state::difference_bound_matrix::DifferenceBoundMatrix;

pub mod difference_bound_matrix;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct SymbolicState {
    location: String,
    zone: DifferenceBoundMatrix,
}

impl SymbolicState {
    pub fn new(location_name: &str, zone: DifferenceBoundMatrix) -> SymbolicState {
        SymbolicState {
            location: String::from(location_name),
            zone,
        }
    }

    pub fn location(&self) -> &String {
        &self.location
    }

    pub fn zone(&self) -> &DifferenceBoundMatrix {
        &self.zone
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_returns_correct_symbolic_state_when_called() {
        // given
        let location_name = "init";
        let zone = DifferenceBoundMatrix::for_initial_symbolic_state(1);

        // when
        let result = SymbolicState::new(location_name, zone.clone());

        // then
        assert_eq!(result.location, location_name);
        assert_eq!(result.zone, zone);
    }
}
