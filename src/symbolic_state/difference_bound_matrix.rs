use crate::ta::clock::Clock;
use crate::ta::clock_constraint::ClockConstraint;
use crate::ta::clock_constraint::clause::{Clause, ClockComparator};
use std::cmp;

const UNBOUNDED_ENTRY: i32 = i32::MAX;

/// Efficient representation of clock constraints.
/// See "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi for more information
/// on DBMs.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct DifferenceBoundMatrix {
    // Implementation details:
    // - see "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi for more
    //   explanations of the encoding details
    // - for efficiency reasons, the two-dimensional matrix is stored in a one-dimensional vector
    // - entries are accessed as follows: entry(row,column) = row * size + column, where size is the
    //   number of rows/columns (e.g., 3 for a 3x3 matrix)
    // - unbounded entries (infinity) are stored as i32::MAX
    // - strictness of the bound of an entry is stored in the least significant bit of an entry
    // - strict bounds (i.e., "<") are stored as an unset bit (i.e., 0)
    // - non-strict bounds (i.e., "<=") are stored as a set bit (i.e., 1)
    // - due to the strictness encoding, the numeric value of the entry is shifted by one bit
    entries: Vec<i32>,
    size: usize,
}

impl DifferenceBoundMatrix {
    /// Constructs the DBM for the initial symbolic state.
    pub fn for_initial_symbolic_state(number_of_clocks: usize) -> DifferenceBoundMatrix {
        let size = number_of_clocks + 1; // + 1 for reference clock "zero"
        let leq_0 = encode_dbm_entry(0, ClockComparator::LEQ);
        DifferenceBoundMatrix {
            entries: vec![leq_0; size * size],
            size,
        }
    }

    /// Returns the entry at `(row, column)` where the top left element of the matrix has index
    /// `(0,0)`.
    ///
    /// # Panics
    /// Panics in case of an out-of-bounds access.
    fn get(&self, row: usize, column: usize) -> i32 {
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
    fn set(&mut self, row: usize, column: usize, val: i32) {
        if row > self.size - 1 || column > self.size - 1 {
            panic!(
                "Tried to set entry ({}, {}) in a matrix with dimensions {} x {}",
                row, column, self.size, self.size
            );
        }

        let translated_pos = row * self.size + column;
        self.entries[translated_pos] = val;
    }

    /// Applies the `and` operator with the provided clock constraint to the DBM. The set of all
    /// clocks is needed to determine each clock's position in the DBM.
    ///
    /// # None Return
    /// This method returns `None` if and only if the resulting DBM would be unsatisfiable.
    ///
    /// # Panics
    /// Panics if the set of all clocks is not sorted by name. This is to ensure that the DBM
    /// entries are always set to the correct field.
    pub fn and(&mut self, cc: &ClockConstraint, all_clocks_sorted: &Vec<Clock>) -> Option<()> {
        panic_if_clocks_not_sorted(all_clocks_sorted);

        for clause in cc.clauses() {
            self.and_clause(clause, all_clocks_sorted)?;
        }

        panic_if_clock_diffs_to_self(self);
        Some(())
    }

    /// Applies the `and` operator with the provided clause to the DBM. The resulting DBM is
    /// canonical if the input DBM was canonical.
    ///
    /// The set of all clocks is needed to determine each clock's position in the DBM. For more
    /// information, see Algorithm 8 of "Timed Automata: Semantics, Algorithms and Tools" by
    /// Bengtsson and Yi.
    ///
    /// # None Return
    /// This method returns `None` if and only if the resulting DBM would be unsatisfiable.
    fn and_clause(&mut self, clause: &Clause, all_clocks_sorted: &Vec<Clock>) -> Option<()> {
        // DBMs only have < and <= in entries, i.e., > and >= need to be "translated"
        let clock_pos = find_clock_pos_in_dbm(clause.lhs(), all_clocks_sorted);
        let (row, column) = match clause.op() {
            ClockComparator::GEQ | ClockComparator::GREATER => (0, clock_pos),
            ClockComparator::LEQ | ClockComparator::LESSER => (clock_pos, 0),
        };
        let encoded_value = match clause.op() {
            ClockComparator::GEQ => encode_dbm_entry(-(clause.rhs() as i32), ClockComparator::LEQ),
            ClockComparator::GREATER => {
                encode_dbm_entry(-(clause.rhs() as i32), ClockComparator::LESSER)
            }
            op => encode_dbm_entry(clause.rhs() as i32, op),
        };

        // check satisfiability
        // NOTE: Algorithm 8 in paper says "<", but "<=" is correct in next line
        if add_encoded_dbm_entries(self.get(column, row), encoded_value) <= 0 {
            self.set(0, 0, encode_dbm_entry(-1, ClockComparator::LEQ));
            return None;
        }

        // if current clause is less strict -> do nothing
        if encoded_value >= self.get(row, column) {
            return Some(());
        }

        // set new value and compute canonical form
        self.set(row, column, encoded_value);
        for i in 0..self.size {
            for j in 0..self.size {
                let d_ix = self.get(i, row);
                let d_xj = self.get(row, j);
                let d_ix_plus_d_xj = add_encoded_dbm_entries(d_ix, d_xj);
                if d_ix_plus_d_xj < self.get(i, j) {
                    self.set(i, j, d_ix_plus_d_xj);
                }
                let d_iy = self.get(i, column);
                let d_yj = self.get(column, j);
                let d_iy_plus_d_yj = add_encoded_dbm_entries(d_iy, d_yj);
                if d_iy_plus_d_yj < self.get(i, j) {
                    self.set(i, j, d_iy_plus_d_yj);
                }
            }
        }

        panic_if_clock_diffs_to_self(self);
        Some(())
    }

    /// Applies the `up` operation to the DBM. The resulting DBM is canonical if the input DBM was
    /// canonical. For more information, see Algorithm 6 of "Timed Automata: Semantics, Algorithms
    /// and Tools" by Bengtsson and Yi.
    pub fn up(&mut self) {
        // start at index 1 because index 0 is special clock "zero"
        for i in 1..self.size {
            self.set(i, 0, UNBOUNDED_ENTRY);
        }

        panic_if_clock_diffs_to_self(self);
    }

    /// Applies the `reset` operator to the DBM. The resulting DBM is canonical if the input DBM was
    /// canonical.
    ///
    /// The set of all clocks is needed to determine each clock's position in the DBM. For more
    /// information, see Algorithm 10 of "Timed Automata: Semantics, Algorithms and Tools" by
    /// Bengtsson and Yi.
    ///
    /// # Panics
    /// Panics if the set of all clocks is not sorted by name. This is to ensure that the DBM
    /// entries are always set to the correct field.
    pub fn reset(&mut self, reset: &Vec<Clock>, all_clocks_sorted: &Vec<Clock>) {
        panic_if_clocks_not_sorted(all_clocks_sorted);

        let leq_0_enc = encode_dbm_entry(0, ClockComparator::LEQ);
        for clock in reset {
            let pos_in_dbm = find_clock_pos_in_dbm(clock, all_clocks_sorted);
            for i in 0..self.size {
                let val_xi = add_encoded_dbm_entries(leq_0_enc, self.get(0, i));
                self.set(pos_in_dbm, i, val_xi);
                let val_ix = add_encoded_dbm_entries(self.get(i, 0), leq_0_enc);
                self.set(i, pos_in_dbm, val_ix);
            }
        }

        panic_if_clock_diffs_to_self(self);
    }

    /// Applies k-normalization to the DBM. The resulting DBM is canonical if the input DBM was
    /// canonical. For more information, see Algorithm 13 of "Timed Automata: Semantics, Algorithms
    /// and Tools" by Bengtsson and Yi.
    pub fn k_norm(&mut self, k: i32) {
        let k_leq_enc = encode_dbm_entry(k, ClockComparator::LEQ);
        let minus_k_lesser_enc = encode_dbm_entry(-k, ClockComparator::LESSER);
        let mut changed_dbm = false;

        for i in 0..self.size {
            for j in 0..self.size {
                let d_ij = self.get(i, j);

                if i == j || d_ij == UNBOUNDED_ENTRY {
                    continue;
                }

                if d_ij > k_leq_enc {
                    self.set(i, j, UNBOUNDED_ENTRY);
                    changed_dbm = true;
                } else if d_ij < minus_k_lesser_enc {
                    self.set(i, j, minus_k_lesser_enc);
                    changed_dbm = true;
                }
            }
        }

        panic_if_clock_diffs_to_self(self);

        // re-compute canonical form in case of any changes
        if changed_dbm {
            self.close();
        }
    }

    /// Computes the canonical version of a DBM by using Floyd's algorithm for shortest paths. For
    /// more information, see Algorithm 2 of "Timed Automata: Semantics, Algorithms and Tools" by
    /// Bengtsson and Yi.
    fn close(&mut self) {
        for k in 0..self.size {
            for i in 0..self.size {
                for j in 0..self.size {
                    let d_ij = self.get(i, j);
                    let d_ik = self.get(i, k);
                    let d_kj = self.get(k, j);
                    self.set(i, j, cmp::min(d_ij, add_encoded_dbm_entries(d_ik, d_kj)));
                }
            }
        }

        panic_if_clock_diffs_to_self(self);
    }
}

/// Encodes a DBM entry into an efficient representation. See "Timed Automata: Semantics,
/// Algorithms and Tools" by Bengtsson and Yi for details.
fn encode_dbm_entry(val: i32, clock_comparator: ClockComparator) -> i32 {
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

fn decode_dbm_entry(encoded_entry: i32) -> (i32, ClockComparator) {
    let comparator = if encoded_entry & 1 == 1 {
        ClockComparator::LEQ
    } else {
        ClockComparator::LESSER
    };
    (encoded_entry >> 1, comparator)
}

/// Performs addition of encoded DBM entries directly on the encoding. See "Timed Automata:
/// Semantics, Algorithms and Tools" by Bengtsson and Yi for details.
fn add_encoded_dbm_entries(first: i32, second: i32) -> i32 {
    // See Algorithm 17 in "Timed Automata: Semantics, Algorithms and Tools" by Bengtsson and Yi
    if first == UNBOUNDED_ENTRY || second == UNBOUNDED_ENTRY {
        return UNBOUNDED_ENTRY;
    }
    first + second - ((first & 1) | (second & 1))
}

fn find_clock_pos_in_dbm(clock: &Clock, all_clocks: &Vec<Clock>) -> usize {
    for (i, clock_from_vec) in all_clocks.iter().enumerate() {
        if clock == clock_from_vec {
            return i + 1; // + 1 because of special clock "zero" in DBMs
        }
    }
    panic!("Clock {clock} not contained in {all_clocks:?}");
}

fn panic_if_clocks_not_sorted(clocks: &Vec<Clock>) {
    let is_sorted = clocks.windows(2).all(|cw| cw[0].name() <= cw[1].name());
    if !is_sorted {
        panic!("Clocks are not sorted by name: {clocks:?}");
    }
}

/// Panics if the difference of any clock to itself (i.e., all entries `(i, i)`) is not `(0, <=)`.
fn panic_if_clock_diffs_to_self(dbm: &DifferenceBoundMatrix) {
    let leq_0_enc = encode_dbm_entry(0, ClockComparator::LEQ);
    for i in 0..dbm.size {
        if dbm.get(i, i) != leq_0_enc {
            let (val, comp) = decode_dbm_entry(dbm.get(i, i));
            let comp_str = match comp {
                ClockComparator::LESSER => "<",
                ClockComparator::LEQ => "<=",
                ClockComparator::GEQ => ">=",
                ClockComparator::GREATER => ">",
            };
            panic!("Entry at ({i}, {i}) should be (0, <=), but entry is ({val}, {comp_str})");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ta::clock_constraint::clause::ClockComparator::LESSER;

    #[test]
    fn for_initial_symbolic_state_creates_vector_with_exact_capacity_when_called() {
        // given
        let size = 3;
        let expected_capacity = (size + 1) * (size + 1); // + 1 for clock "zero"

        // when
        let result = DifferenceBoundMatrix::for_initial_symbolic_state(size);

        // then
        assert_eq!(result.entries.capacity(), expected_capacity);
    }

    #[test]
    fn for_initial_symbolic_state_creates_vector_with_all_entries_set_to_leq_0() {
        // given
        let size = 3;
        let leq_0_encoded = encode_dbm_entry(0, ClockComparator::LEQ);

        // when
        let result = DifferenceBoundMatrix::for_initial_symbolic_state(size);

        // then
        assert!(!result.entries.is_empty());
        for entry in result.entries {
            assert_eq!(entry, leq_0_encoded);
        }
    }

    #[test]
    fn get_works_when_accessing_top_left_element() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size,
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
            size,
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
        let dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size,
        };

        // when / then
        dbm.get(size + 1, size + 1);
    }

    #[test]
    fn get_and_set_access_the_same_elements_when_called() {
        // given
        let size = 3;
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size,
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
            size,
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
            size,
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
            size,
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
        let mut dbm = DifferenceBoundMatrix {
            entries: vec![1; size * size],
            size,
        };

        // when / then
        dbm.set(size + 1, size + 1, 42);
    }

    #[test]
    fn and_works_correctly_when_input_has_single_clause() {
        // given
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        dbm.up();

        let val = 5;
        let op = ClockComparator::LESSER;
        let clause = Clause::new(&clock, op, val);
        let cc = ClockConstraint::new(Box::from(vec![clause]));

        let mut dbm_expected = dbm.clone();
        dbm_expected.set(1, 0, encode_dbm_entry(val as i32, op));

        // when
        let result = dbm.and(&cc, &clocks);

        // then
        assert!(result.is_some());
        assert_eq!(dbm, dbm_expected);
    }

    #[test]
    fn and_does_nothing_when_input_has_no_clauses() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.up();
        let cc = ClockConstraint::new(Box::from(vec![]));
        let dbm_expected = dbm.clone();

        // when
        let result = dbm.and(&cc, &vec![]);

        // then
        assert!(result.is_some());
        assert_eq!(dbm, dbm_expected);
    }

    #[test]
    fn and_works_correctly_when_input_has_multiple_clauses_with_single_clock() {
        // given
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        dbm.up();

        let clause_0 = Clause::new(&clock, ClockComparator::LESSER, 5);
        let val_1 = 3;
        let op_1 = ClockComparator::LEQ;
        let clause_1 = Clause::new(&clock, op_1, val_1);
        let cc = ClockConstraint::new(Box::from(vec![clause_0, clause_1]));

        let mut dbm_expected = dbm.clone();
        dbm_expected.set(1, 0, encode_dbm_entry(val_1 as i32, op_1));

        // when
        let result = dbm.and(&cc, &clocks);

        // then
        assert!(result.is_some());
        assert_eq!(dbm, dbm_expected);
    }

    #[test]
    fn and_computes_canonical_dbm_when_input_has_multiple_clauses_with_multiple_clocks() {
        // given
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");
        let clocks = vec![clock_x.clone(), clock_y.clone()];

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        dbm.up();

        let clause_0 = Clause::new(&clock_x, ClockComparator::LESSER, 5);
        let val_1 = 3;
        let op_1 = ClockComparator::LEQ;
        let clause_1 = Clause::new(&clock_y, op_1, val_1);
        let cc = ClockConstraint::new(Box::from(vec![clause_0, clause_1]));

        let mut dbm_expected = dbm.clone();
        // val_1 / op_1 in both cases as this is stricter (and result should be canonical)
        dbm_expected.set(1, 0, encode_dbm_entry(val_1 as i32, op_1));
        dbm_expected.set(2, 0, encode_dbm_entry(val_1 as i32, op_1));

        // when
        let result = dbm.and(&cc, &clocks);

        // then
        assert!(result.is_some());
        assert_eq!(dbm, dbm_expected);
    }

    #[test]
    fn and_returns_none_when_result_is_unsatisfiable() {
        // given
        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(clocks.len());
        dbm.up();

        let clause_0 = Clause::new(&clock, ClockComparator::GREATER, 5);
        let clause_1 = Clause::new(&clock, ClockComparator::LEQ, 3);
        let cc = ClockConstraint::new(Box::from(vec![clause_0, clause_1]));

        // when
        let result = dbm.and(&cc, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_works_correctly_when_result_is_satisfiable_with_geq_leq() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.up();
        // following line is x >= 5 as it is set in first row for comparison with clock zero
        dbm.set(0, 1, encode_dbm_entry(-5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let val = 5;
        let op = ClockComparator::LEQ;
        let clause = Clause::new(&clock, op, val);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_some());
        let added_constraint_decoded = decode_dbm_entry(dbm.get(1, 0));
        assert_eq!(added_constraint_decoded, (val as i32, op));
    }

    #[test]
    fn and_clause_returns_none_when_result_is_unsatisfiable_with_greater_lesser() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        // following line is x > 5 as it is set in first row for comparison with clock zero
        dbm.set(0, 1, encode_dbm_entry(-5, ClockComparator::LESSER));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::LESSER, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_returns_none_when_result_is_unsatisfiable_with_geq_lesser() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        // following line is x >= 5 as it is set in first row for comparison with clock zero
        dbm.set(0, 1, encode_dbm_entry(-5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::LESSER, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_returns_none_when_result_is_unsatisfiable_with_lesser_greater() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LESSER));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::GREATER, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_returns_none_when_result_is_unsatisfiable_with_leq_greater() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::GREATER, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_returns_none_when_result_is_unsatisfiable_with_greater_leq() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        // following line is x > 5 as it is set in first row for comparison with clock zero
        dbm.set(0, 1, encode_dbm_entry(-5, ClockComparator::LESSER));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::LEQ, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_works_correctly_when_result_is_unsatisfiable_with_leq_greater() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let clause = Clause::new(&clock, ClockComparator::GREATER, 5);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_none());
    }

    #[test]
    fn and_clause_works_correctly_when_result_is_satisfiable_with_leq_leq() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let val = 5;
        let op = ClockComparator::LEQ;
        let clause = Clause::new(&clock, op, val);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_some());
        let added_constraint_decoded = decode_dbm_entry(dbm.get(1, 0));
        assert_eq!(added_constraint_decoded, (val as i32, op));
        let lower_bound_decoded = decode_dbm_entry(dbm.get(0, 1));
        assert_eq!(lower_bound_decoded, (0, ClockComparator::LEQ));
    }

    #[test]
    fn and_clause_works_correctly_when_result_is_satisfiable_with_leq_lesser() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LEQ));

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let val = 5;
        let op = ClockComparator::LESSER;
        let clause = Clause::new(&clock, op, val);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_some());
        let added_constraint_decoded = decode_dbm_entry(dbm.get(1, 0));
        assert_eq!(added_constraint_decoded, (val as i32, op));
        let lower_bound_decoded = decode_dbm_entry(dbm.get(0, 1));
        assert_eq!(lower_bound_decoded, (0, ClockComparator::LEQ));
    }

    #[test]
    fn and_clause_does_nothing_when_clause_is_less_strict() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        dbm.set(1, 0, encode_dbm_entry(5, ClockComparator::LESSER));
        let dbm_expected = dbm.clone();

        let clock = Clock::new("x");
        let clocks = vec![clock.clone()];
        let val = 5;
        let op = ClockComparator::LEQ;
        let clause = Clause::new(&clock, op, val);

        // when
        let result = dbm.and_clause(&clause, &clocks);

        // then
        assert!(result.is_some());
        assert_eq!(dbm, dbm_expected)
    }

    #[test]
    fn up_works_correctly_when_dbm_has_single_clock() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(1);
        let mut expected_dbm = dbm.clone();
        expected_dbm.set(1, 0, UNBOUNDED_ENTRY);

        // when
        dbm.up();

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn up_works_correctly_when_dbm_has_multiple_clocks() {
        // given
        let number_of_clocks = 10;
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(number_of_clocks);

        let mut expected_dbm = dbm.clone();
        for i in 0..number_of_clocks {
            expected_dbm.set(i + 1, 0, UNBOUNDED_ENTRY); // + 1 because of clock zero
        }

        // when
        dbm.up();

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn up_does_nothing_when_dbm_only_consists_of_internal_clock_zero() {
        // given
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(0);
        let expected_dbm = dbm.clone();

        // when
        dbm.up();

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn reset_resets_to_0_when_called_with_single_clock() {
        // given
        let clock_x = Clock::new("x");
        let all_clocks = vec![clock_x.clone()];

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(all_clocks.len());
        let leq_42_enc = encode_dbm_entry(42, ClockComparator::LEQ);
        let lesser_minus_12_enc = encode_dbm_entry(-12, LESSER);
        dbm.set(1, 0, leq_42_enc); // x <= 42
        dbm.set(0, 1, lesser_minus_12_enc); // x > 12

        // when
        dbm.reset(&vec![clock_x], &all_clocks);

        // then
        assert_eq!(
            dbm,
            DifferenceBoundMatrix::for_initial_symbolic_state(all_clocks.len())
        );
    }

    #[test]
    fn reset_updates_difference_constraints_correctly_when_called_with_multiple_clocks() {
        // given
        let clock_x = Clock::new("x");
        let clock_y = Clock::new("y");
        let all_clocks = vec![clock_x.clone(), clock_y.clone()];

        let clause_x_geq_42 = Clause::new(&clock_x, ClockComparator::GEQ, 42);
        let clause_y_leq_50 = Clause::new(&clock_y, ClockComparator::LEQ, 50);
        let cc = ClockConstraint::new(Box::from(vec![clause_x_geq_42, clause_y_leq_50]));

        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(all_clocks.len());
        dbm.up();
        dbm.and(&cc, &all_clocks);

        let mut expected_dbm = DifferenceBoundMatrix::for_initial_symbolic_state(all_clocks.len());
        let leq_minus_42_enc = encode_dbm_entry(-42, ClockComparator::LEQ);
        let leq_50_enc = encode_dbm_entry(50, ClockComparator::LEQ);
        expected_dbm.set(2, 0, leq_50_enc); // y <= 50
        expected_dbm.set(0, 2, leq_minus_42_enc); // y >= 42
        expected_dbm.set(1, 2, leq_minus_42_enc); // y - x >= 42
        expected_dbm.set(2, 1, leq_50_enc); // y - x <= 50

        // when
        dbm.reset(&vec![clock_x], &all_clocks);

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn k_norm_normalizes_dbm_when_input_is_not_normalized() {
        // given
        // x <= 10 AND y <= 40 AND y - x == 30; k = 20 -> x <= 10 AND y > 20 AND y - x > 20
        let k = 20;
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let leq_10_enc = encode_dbm_entry(10, ClockComparator::LEQ);
        let leq_30_enc = encode_dbm_entry(30, ClockComparator::LEQ);
        let leq_minus_30_enc = encode_dbm_entry(-30, ClockComparator::LEQ);
        let leq_40_enc = encode_dbm_entry(40, ClockComparator::LEQ);
        dbm.set(1, 0, leq_10_enc); // x <= 10
        dbm.set(2, 0, leq_40_enc); // y <= 40
        dbm.set(2, 1, leq_30_enc); // y - x <= 30
        dbm.set(1, 2, leq_minus_30_enc); // y - x >= 30

        let mut expected_dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let lesser_minus_20_enc = encode_dbm_entry(-20, ClockComparator::LESSER);
        expected_dbm.set(1, 0, leq_10_enc); // x <= 10
        expected_dbm.set(0, 2, lesser_minus_20_enc); // y > 20
        expected_dbm.set(2, 0, UNBOUNDED_ENTRY); // y <= INFINITY
        expected_dbm.set(2, 1, UNBOUNDED_ENTRY); // y - x <= INFINITY
        expected_dbm.set(1, 2, lesser_minus_20_enc); // y - x > 20

        // when
        dbm.k_norm(k);

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn k_norm_does_nothing_when_input_is_already_normalized() {
        // given
        // x <= 10 AND y <= 10 AND x == y; k = 20
        let k = 20;
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let leq_10_enc = encode_dbm_entry(10, ClockComparator::LEQ);
        dbm.set(1, 0, leq_10_enc); // x <= 10
        dbm.set(2, 0, leq_10_enc); // y <= 10

        let expected_dbm = dbm.clone();

        // when
        dbm.k_norm(k);

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn close_computes_canonical_dbm_when_input_is_not_canonical() {
        // given
        // x <= 3 AND y <= 5 AND x == y -> canonical: x <= 3 AND y <= 3 AND x == <
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let leq_3_enc = encode_dbm_entry(3, ClockComparator::LEQ);
        let leq_5_enc = encode_dbm_entry(5, ClockComparator::LEQ);
        dbm.set(1, 0, leq_3_enc);
        dbm.set(2, 0, leq_5_enc);

        let mut expected_dbm = dbm.clone();
        expected_dbm.set(2, 0, leq_3_enc);

        // when
        dbm.close();

        // then
        assert_eq!(dbm, expected_dbm);
    }

    #[test]
    fn close_does_nothing_when_input_is_canonical() {
        // given
        // x <= 3 AND y <= 3 AND x == y already is canonical
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let leq_3_enc = encode_dbm_entry(3, ClockComparator::LEQ);
        dbm.set(1, 0, leq_3_enc);
        dbm.set(2, 0, leq_3_enc);

        let expected_dbm = dbm.clone();

        // when
        dbm.close();

        // then
        assert_eq!(dbm, expected_dbm);
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
    fn encode_dbm_entry_correctly_encodes_entry_when_value_is_negative() {
        // given
        let val = -42;
        let comp = ClockComparator::LEQ;

        // when
        let result = encode_dbm_entry(val, comp);

        // then
        assert_eq!(result, (val << 1) + 1);
        assert!(result < 0);
    }

    #[test]
    #[should_panic]
    fn encode_dbm_entry_panics_when_comparator_is_not_lesser_or_leq() {
        // when / then
        encode_dbm_entry(42, ClockComparator::GEQ);
    }

    #[test]
    fn decode_dbm_entry_decodes_correctly_when_comp_is_strict() {
        // given
        let val = 42;
        let comp = ClockComparator::LESSER;
        let encoded_val = val << 1;

        // when
        let result = decode_dbm_entry(encoded_val);

        // then
        assert_eq!(result, (val, comp));
    }

    #[test]
    fn decode_dbm_entry_decodes_correctly_when_comp_is_non_strict() {
        // given
        let val = 42;
        let comp = ClockComparator::LEQ;
        let encoded_val = (val << 1) + 1;

        // when
        let result = decode_dbm_entry(encoded_val);

        // then
        assert_eq!(result, (val, comp));
    }

    #[test]
    fn decode_dbm_entry_decodes_correctly_when_val_is_negative() {
        // given
        let val = -42;
        let comp = ClockComparator::LEQ;
        let encoded_val = (val << 1) + 1;

        // when
        let result = decode_dbm_entry(encoded_val);

        // then
        assert_eq!(result, (val, comp));
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

    #[test]
    fn find_clock_pos_in_dbm_finds_correct_position_when_vec_contains_clock() {
        // given
        let clock_name = "x";
        let clock = Clock::new(clock_name);
        let clocks = vec![clock.clone()];

        // when
        let result = find_clock_pos_in_dbm(&clock, &clocks);

        // then
        assert_eq!(result, 1); // "1" because "0" is special clock "zero"
    }

    #[test]
    #[should_panic]
    fn find_clock_pos_in_dbm_panics_when_vec_does_not_contain_clock() {
        // given
        let clock_name = "x";
        let clock = Clock::new(clock_name);
        let clocks = vec![Clock::new(&(String::from(clock_name) + "other"))];

        // when / then
        find_clock_pos_in_dbm(&clock, &clocks);
    }

    #[test]
    fn panic_if_clocks_not_sorted_does_not_panic_when_clocks_are_sorted() {
        // given
        let clocks = vec![Clock::new("a"), Clock::new("bbb"), Clock::new("z")];

        // when / then
        panic_if_clocks_not_sorted(&clocks); // should not panic
    }

    #[test]
    fn panic_if_clocks_not_sorted_does_not_panic_when_clocks_are_empty() {
        // given
        let clocks = vec![];

        // when / then
        panic_if_clocks_not_sorted(&clocks); // should not panic
    }

    #[test]
    fn panic_if_clocks_not_sorted_does_not_panic_when_exactly_one_clock() {
        // given
        let clocks = vec![Clock::new("a")];

        // when / then
        panic_if_clocks_not_sorted(&clocks); // should not panic
    }

    #[test]
    #[should_panic]
    fn panic_if_clocks_not_sorted_panics_when_clocks_are_not_sorted() {
        // given
        let clocks = vec![Clock::new("a"), Clock::new("z"), Clock::new("b")];

        // when / then
        panic_if_clocks_not_sorted(&clocks);
    }

    #[test]
    fn panic_if_clock_diffs_to_self_does_not_panic_when_clock_eq_to_self() {
        // given
        let dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);

        // when / then
        // following line should not panic
        panic_if_clock_diffs_to_self(&dbm);
    }

    #[test]
    #[should_panic]
    fn panic_if_clock_diffs_to_self_panics_when_clock_diffs_to_self() {
        // given
        let size = 4;
        let mut dbm = DifferenceBoundMatrix::for_initial_symbolic_state(2);
        let leq_42_enc = encode_dbm_entry(42, ClockComparator::LEQ);
        dbm.set(size / 2, size / 2, leq_42_enc);

        // when / then
        // following line should panic
        panic_if_clock_diffs_to_self(&dbm);
    }
}
