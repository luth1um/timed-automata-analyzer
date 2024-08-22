pub fn vecs_eq_without_order<T: PartialEq>(first: &Vec<T>, second: &Vec<T>) -> bool {
    if first.len() != second.len() {
        return false;
    }

    for element in first {
        if !second.contains(element) {
            return false;
        }
    }

    for element in second {
        if !first.contains(element) {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vecs_eq_without_order_returns_true_when_vecs_contain_same_elements_in_same_order() {
        // given
        let vec0 = vec!["a"];
        let vec1 = vec!["a"];

        // when
        let result = vecs_eq_without_order(&vec0, &vec1);

        // then
        assert!(result);
    }

    #[test]
    fn vecs_eq_without_order_returns_true_when_both_vecs_are_empty() {
        // given
        let vec0 = Vec::<&str>::new();
        let vec1 = Vec::<&str>::new();

        // when
        let result = vecs_eq_without_order(&vec0, &vec1);

        // then
        assert!(result);
    }

    #[test]
    fn vecs_eq_without_order_returns_true_when_vecs_contain_same_elements_in_different_order() {
        // given
        let vec0 = vec!["a", "b"];
        let vec1 = vec!["b", "a"];

        // when
        let result = vecs_eq_without_order(&vec0, &vec1);

        // then
        assert!(result);
    }

    #[test]
    fn vecs_eq_without_order_returns_false_when_vecs_have_different_length() {
        // given
        let vec0 = vec!["a", "b"];
        let vec1 = vec!["a"];

        // when
        let result = vecs_eq_without_order(&vec0, &vec1);

        // then
        assert!(!result);
    }

    #[test]
    fn vecs_eq_without_order_returns_false_when_vecs_have_same_length_but_different_elements() {
        // given
        let vec0 = vec!["a", "b"];
        let vec1 = vec!["c", "a"];

        // when
        let result = vecs_eq_without_order(&vec0, &vec1);

        // then
        assert!(!result);
    }
}
