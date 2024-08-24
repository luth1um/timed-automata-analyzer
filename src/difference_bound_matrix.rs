use crate::ta::clock_constraint::clause::ClockComparator;

const UNBOUNDED_ENTRY: u32 = u32::MAX;

/// Efficient representation of clock constraints.
/// See "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi for more information
/// on DBMs.
pub struct DifferenceBoundMatrix {
    // Implementation details:
    // - see "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi for more
    //   explanations of the encoding details
    // - for efficiency reasons, the two-dimensional matrix is stored in a one-dimensional vector
    // - entries are accessed as follows: entry(row,column) = row * size + column, where size is the
    //   number of rows/columns (e.g., 3 for a 3x3 matrix)
    // - unbounded entries (infinity) are stored as u32::MAX
    // - strictness of the bound of an entry is stored in the least significant bit of an entry
    // - strict bounds (i.e., "<") are stored as an unset bit (i.e., 0)
    // - non-strict bounds (i.e., "<=") are stored as a set bit (i.e., 1)
    // - due to the strictness encoding, the numeric value of the entry is shifted by one bit
    entries: Vec<u32>,
    size: usize,
}

impl DifferenceBoundMatrix {
    /// Constructs a new square DBM with dimensions `size x size`.
    pub fn with_size(size: usize) -> DifferenceBoundMatrix {
        // TODO: Do I need this? It might be better to have something like from_clock_constraint(cc, all_clocks)
        DifferenceBoundMatrix {
            entries: Vec::with_capacity(size * size),
            size,
        }
    }

    /// Returns the entry at `(row, column)` where the top left element of the matrix has index
    /// `(0,0)`.
    ///
    /// # Panics
    /// Panics in case of an out-of-bounds access.
    fn get(&self, row: usize, column: usize) -> u32 {
        if row > self.size - 1 || column > self.size - 1 {
            panic!(
                "Tried to get entry ({}, {}) in a matrix with dimensions {} x {}",
                row, column, self.size, self.size
            );
        }
        let translated_pos = row * self.size + column;
        match self.entries.get(translated_pos) {
            Some(entry) => *entry,
            None => panic!(
                "Tried to access entry ({}, {}) at translated position {} in vector of size {}",
                row,
                column,
                translated_pos,
                self.entries.len()
            ),
        }
    }

    /// Sets the entry at `(row, column)` where the top left element of the matrix has index `(0,0)`.
    ///
    /// # Panics
    /// Panics in case of an out-of-bounds access.
    fn set(&mut self, row: usize, column: usize, val: u32) {
        if row > self.size - 1 || column > self.size - 1 {
            panic!(
                "Tried to set entry ({}, {}) in a matrix with dimensions {} x {}",
                row, column, self.size, self.size
            );
        }

        let translated_pos = row * self.size + column;
        self.entries[translated_pos] = val;
    }
}

/// Encodes a DBM entry into an efficient representation. See "Timed Automata: Semantics,
/// Algorithms and Tools" by Bengtsson and Yi for details.
fn encode_dbm_entry(val: u32, clock_comparator: ClockComparator) -> u32 {
    match clock_comparator {
        ClockComparator::LESSER => val << 1,
        ClockComparator::LEQ => (val << 1) + 1,
        ClockComparator::GEQ => {
            panic!("Tried to encode comparator >= into DBM entry, but only < and <= allowed")
        }
        ClockComparator::GREATER => {
            panic!("Tried to encode comparator > into DBM entry, but only < and <= allowed")
        }
    }
}

/// Performs addition of encoded DBM entries directly on the encoding. See "Timed Automata:
/// Semantics, Algorithms and Tools" by Bengtsson and Yi for details.
fn add_encoded_dbm_entries(first: u32, second: u32) -> u32 {
    // See Algorithm 17 in "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi
    if first == UNBOUNDED_ENTRY || second == UNBOUNDED_ENTRY {
        return UNBOUNDED_ENTRY;
    }
    first + second - ((first & 1) | (second & 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn with_size_returns_dbm_with_correct_size_when_called() {
        // TODO: implement (if the method is actually needed)
    }

    #[test]
    fn get_works_when_accessing_top_left_element() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size
        };
        let val = 42;
        dbm.entries[0] = val;

        // when
        let result = dbm.get(0, 0);

        // then
        assert_eq!(result, val);
    }

    #[test]
    fn get_works_when_accessing_bottom_right_element() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size
        };
        let val = 42;
        dbm.entries[size * size - 1] = val;

        // when
        let result = dbm.get(size - 1, size - 1);

        // then
        assert_eq!(result, val);
    }

    #[test]
    #[should_panic]
    fn get_panics_when_access_is_out_of_bounds() {
        // given
        let size = 3;
        let dbm = DifferenceBoundMatrix::with_size(3);

        // when / then
        dbm.get(size + 1, size + 1);
    }

    #[test]
    fn get_and_set_access_the_same_elements_when_called() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size
        };

        let row = 1;
        let column = 1;
        let val = 42;

        // when
        dbm.set(row, column, val);
        let result = dbm.get(row, column);

        // then
        assert_eq!(result, val);
    }

    #[test]
    fn set_works_when_accessing_top_left_element() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size
        };
        let val = 42;

        // when
        dbm.set(0, 0, val);

        // then
        assert_eq!(dbm.entries[0], val);
    }

    #[test]
    fn set_works_when_accessing_bottom_right_element() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size
        };
        let val = 42;

        // when
        dbm.set(size - 1, size - 1, val);

        // then
        assert_eq!(dbm.entries[size * size - 1], val);
    }

    #[test]
    fn set_does_not_change_length_of_entries_vector() {
        // given
        let size = 3;
        let len_init = size * size;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; len_init],
            size
        };

        // when
        dbm.set(0, 0, 42);

        // then
        assert_eq!(dbm.entries.len(), len_init);
    }

    #[test]
    #[should_panic]
    fn set_panics_when_access_is_out_of_bounds() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix::with_size(3);

        // when / then
        dbm.set(size + 1, size + 1, 42);
    }

    #[test]
    fn encode_dbm_entry_correctly_encodes_entry_when_comparator_is_strict() {
        // given
        let val = 42;
        let comp = ClockComparator::LESSER;

        // when
        let result = encode_dbm_entry(val, comp);

        // then
        assert_eq!(result, val << 1);
    }

    #[test]
    fn encode_dbm_entry_correctly_encodes_entry_when_comparator_is_non_strict() {
        // given
        let val = 42;
        let comp = ClockComparator::LEQ;

        // when
        let result = encode_dbm_entry(val, comp);

        // then
        assert_eq!(result, (val << 1) + 1);
    }

    #[test]
    #[should_panic]
    fn encode_dbm_entry_panics_when_comparator_is_not_lesser_or_leq() {
        // when / then
        encode_dbm_entry(42, ClockComparator::GEQ);
    }

    #[test]
    fn add_encoded_dbm_entries_returns_correct_result_when_both_have_strict_bounds() {
        // given
        let first = 42;
        let first_enc = first << 1; // strict bound
        let second = 1234;
        let second_enc = second << 1; // strict bound

        // when
        let result_enc = add_encoded_dbm_entries(first_enc, second_enc);

        // then
        assert_eq!(result_enc & 1, 0); // comparator is strict

        let result_num = result_enc >> 1;
        assert_eq!(result_num, first + second);
    }

    #[test]
    fn add_encoded_dbm_entries_returns_correct_result_when_both_have_non_strict_bounds() {
        // given
        let first = 42;
        let first_enc = (first << 1) + 1; // non-strict bound
        let second = 1234;
        let second_enc = (second << 1) + 1; // non-strict bound

        // when
        let result_enc = add_encoded_dbm_entries(first_enc, second_enc);

        // then
        assert_eq!(result_enc & 1, 1); // comparator is non-strict

        let result_num = result_enc >> 1;
        assert_eq!(result_num, first + second)
    }

    #[test]
    fn add_encoded_dbm_entries_returns_correct_result_when_one_has_strict_bounds() {
        // given
        let first = 42;
        let first_enc = first << 1; // strict bound
        let second = 1234;
        let second_enc = (second << 1) + 1; // non-strict bound

        // when
        let result_enc = add_encoded_dbm_entries(first_enc, second_enc);

        // then
        assert_eq!(result_enc & 1, 0); // comparator is strict

        let result_num = result_enc >> 1;
        assert_eq!(result_num, first + second)
    }

    #[test]
    fn add_encoded_dbm_entries_returns_unbounded_when_first_arg_is_unbounded() {
        // when
        let result = add_encoded_dbm_entries(UNBOUNDED_ENTRY, 17);

        // then
        assert_eq!(result, UNBOUNDED_ENTRY);
    }

    #[test]
    fn add_encoded_dbm_entries_returns_unbounded_when_second_arg_is_unbounded() {
        // when
        let result = add_encoded_dbm_entries(17, UNBOUNDED_ENTRY);

        // then
        assert_eq!(result, UNBOUNDED_ENTRY);
    }
}
