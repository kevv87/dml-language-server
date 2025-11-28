//  © 2024 Intel Corporation
//  SPDX-License-Identifier: Apache-2.0 and MIT
use std::cmp::PartialOrd;

// Sort a collection of T, outputting into potentially a different collection
// such that for each element in the result, no element after will
// be smaller
pub fn partial_sort_by_key<C, E, F, T>(coll: C, f: F) -> Vec<T> where
    C: IntoIterator<Item = T>,
    T: Clone,
    E: PartialOrd,
    F: Fn(T) -> E {
    // TODO: This algorithm can probably be improved

    // Working off the assumption that he ordering is transitive,
    // and that a > b -> b < a we can simply insertion sort
    // by finding the first location where we're definitely
    // larger than something
    let mut result: Vec<T> = vec![];
    for e1 in coll {
        if let Some(insert_index) = result.iter()
            .position(|e2|f(e1.clone()).gt(&f(e2.clone()))) {
            result.insert(insert_index, e1);
        } else {
            result.push(e1.clone());
        }
    }
    result
}

pub fn partial_sort_by_key_in_place<E, F, T>(coll: &mut Vec<T>, f: F)
where
    E: PartialOrd,
    F: Fn(T) -> E,
    T: Clone
{
    let mut result = partial_sort_by_key(coll.drain(..), f);
    coll.append(&mut result);
}
