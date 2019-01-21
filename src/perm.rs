//! Permutations of finite sets.
use std::cmp::max;
use std::fmt;
use std::mem::replace;

use num_integer::Integer;
use num_traits::{FromPrimitive, ToPrimitive};

use crate::action::{LeftAction, RightAction};
use crate::assign::{Assign, AssignFn, AssignValue};
use crate::El;

/// A permutation of a finite set.
///
/// A permutation rearranges the elements of a finite set. It is a bijection from a set to the same
/// set.
///
/// In permafrost these sets are always {0, ..., n-1} for some n of the integer type [`El`].
/// Permutations on another finite set X can be represented by fixing a bijection from X to {0, ...,
/// |X|-1}. The set of permutations of {0, ..., n-1} is called the symmetric group of order n and
/// also written as S<sub>n</sub>.
///
/// Permafrost implicitly extends all permutations to the set of all [`El`]. This means that every
/// permutation can be applied to any [`El`] and any two permutations can be composed.
///
/// Internally a permutation is stored as a vector containing the images of {0, ..., n - 1} for some
/// n. This means that permutations on smaller elements require less storage than permutations on
/// larger elements.
#[derive(Default)]
pub struct Perm {
    // We're not actually using a vector, this way we can ensure that all allocated elements are
    // valid. This makes repeated gorwing and shrinking faster as we only have to update length.
    perm: Box<[El]>,
    length: usize,
}

impl Perm {
    /// The identity permutation.
    pub fn new() -> Perm {
        Perm::default()
    }

    fn initialize_excess_capacity(perm: &mut Vec<El>) {
        while perm.len() < perm.capacity() {
            // Overflow here is ok as we never access elements past self.length
            perm.push(perm.len() as El)
        }
    }

    /// Create a permutation from a vector containing the images of 0..n.
    ///
    /// Returns None if the vector does not correspond to a permutation.
    pub fn from_vec(perm: Vec<El>) -> Option<Perm> {
        Self::from_vec_with_scratch(perm, &mut vec![])
    }

    /// Create a permutation from a vector containing the images of 0..n.
    ///
    /// Returns None if the vector does not correspond to a permutation.
    /// The last parameter is used as scratch space and will be overwritten.
    pub fn from_vec_with_scratch(mut perm: Vec<El>, scratch: &mut Vec<bool>) -> Option<Perm> {
        // Having the size of the perm vec be a valid El itself simplifies some things and allows
        // for some optimizations
        assert!(perm.len() <= El::max_value() as usize);
        let seen = scratch;
        seen.clear();
        seen.resize(perm.len(), false);

        for &p_i in perm.iter() {
            let p_i = p_i as usize;
            if p_i >= perm.len() || seen[p_i] {
                return None;
            }
            seen[p_i] = true;
        }

        let length = perm.len();

        Self::initialize_excess_capacity(&mut perm);

        let mut result = Perm {
            perm: perm.into_boxed_slice(),
            length,
        };

        result.shrink();

        Some(result)
    }

    fn extend_for(&mut self, el: El) {
        // Having the size of the perm vec be a valid El itself simplifies some things and allows
        // for some optimizations
        self.extend_to(el as usize + 1);
    }

    fn extend_to(&mut self, length: usize) {
        if length <= self.length {
            return;
        } else {
            self.resize(length);
        }
    }

    fn resize(&mut self, length: usize) {
        if length > self.perm.len() {
            // Realloc with Vec's resizing strategy
            let old_length = self.perm.len();
            let mut perm = replace(&mut self.perm, Box::new([])).into_vec();
            perm.reserve(length - old_length);

            Self::initialize_excess_capacity(&mut perm);

            self.perm = perm.into_boxed_slice();
        }
        // "clear" everything past the new length up to the old length
        if self.length > length {
            for (i, p_i) in self.perm[length..self.length].iter_mut().enumerate() {
                *p_i = (length + i) as El;
            }
        }
        self.length = length;
    }

    fn resize_uninitialized(&mut self, length: usize) {
        // TODO optimize, just a marker for now
        self.resize(length)
    }

    fn shrink(&mut self) {
        while self.length > 0 && self.perm[self.length - 1] == (self.length - 1) as El {
            self.length -= 1;
        }
    }

    fn perm_slice(&self) -> &[El] {
        &self.perm[..self.length]
    }

    /// Apply a transposition of two elements on the right.
    pub fn right_transpose(&mut self, a: El, b: El) {
        self.extend_for(max(a, b));
        self.perm.swap(a as usize, b as usize);
        self.shrink();
    }

    /// The inverse of this permutation.
    pub fn inverse<'a>(&'a self) -> impl AssignValue<Perm> + 'a {
        AssignFn(move |target: &mut Perm| {
            target.resize_uninitialized(self.perm.len());
            for (i, &p_i) in self.perm.iter().enumerate() {
                let p_i = p_i as usize;
                let i = i as El;
                target.perm[p_i] = i;
            }
            // No need to shrink, support of inverse stays the same
            target.length = self.length;
        })
    }

    /// The square of this permutation.
    pub fn square<'a>(&'a self) -> impl AssignValue<Perm> + 'a {
        AssignFn(move |target: &mut Perm| {
            target.clone_from(self);
            self.right_apply_to(target);
        })
    }

    /// A power of this permutation.
    ///
    /// This implementation performs efficient exponentiation by squaring.
    pub fn pow<E>(&self, exponent: E) -> Power<E> {
        Power {
            base: self,
            exponent,
        }
    }

    /// Return the cycle starting at an element.
    ///
    /// Returns a 1-cycle when the element is not in the support of this permutation.
    pub fn cycle_at(&self, el: El) -> Cycle {
        Cycle {
            perm: self,
            pos: Some(el),
            start: el,
        }
    }

    /// Returns an iterator over all proper cycles of a permutation.
    ///
    /// The returned iterator does not produce any 1-cycles.
    pub fn cycles(&self) -> Cycles {
        self.cycles_with_scratch(Default::default())
    }

    /// Return an iterator over all proper cycles of a permutation. Use existing scratch space.
    ///
    /// The ownership of the scratch space is passed to the returned iterator and can be recovered
    /// by [`Cycles::into_scratch`].
    pub fn cycles_with_scratch(&self, mut scratch: Vec<bool>) -> Cycles {
        scratch.clear();
        scratch.resize(self.perm.len(), false);
        Cycles {
            perm: self,
            seen: scratch,
            pos: 0,
        }
    }

    /// Emit this permutation to a [`Formatter`][fmt::Formatter]. Use existing scratch space.
    ///
    /// When formatting a lot of permutations, reusing the required scratch space using this method
    /// can be more efficient.
    pub fn format_with_scratch(
        &self,
        f: &mut fmt::Formatter,
        scratch: &mut Vec<bool>,
    ) -> fmt::Result {
        let mut cycles = self.cycles_with_scratch(replace(scratch, Default::default()));

        let mut empty = true;

        while let Some(cycle) = cycles.next() {
            empty = false;
            fmt::Display::fmt(&cycle, f)?;
        }

        *scratch = cycles.into_scratch();

        if empty {
            f.write_str("()")?;
        }

        Ok(())
    }
}

impl Clone for Perm {
    fn clone(&self) -> Perm {
        Perm {
            perm: self.perm.clone(),
            length: self.length,
        }
    }

    fn clone_from(&mut self, other: &Perm) {
        self.resize_uninitialized(other.length);
        self.perm[..other.length].copy_from_slice(other.perm_slice());
    }
}

impl From<Perm> for Vec<El> {
    /// This conversion includes excess capacity as vector elements.
    fn from(perm: Perm) -> Vec<El> {
        perm.perm.into_vec()
    }
}

/// Application of a permutation to an element.
impl LeftAction<El, ()> for Perm {
    fn left_apply_with_scratch(&self, el: El, _: &mut ()) -> El {
        self.perm.get(el as usize).cloned().unwrap_or(el)
    }

    fn left_apply_to_with_scratch(&self, el: &mut El, _: &mut ()) {
        *el = self.left_apply(*el);
    }
}

/// Composition of a permutation on the right.
///
/// Unlike composition on the left, this requires no scratch space.
impl RightAction<Perm, ()> for Perm {
    fn right_apply_to_with_scratch(&self, perm: &mut Perm, _: &mut ()) {
        perm.extend_to(self.perm.len());
        for el in perm.perm.iter_mut() {
            self.left_apply_to(el);
        }
        perm.shrink();
    }
}

/// Application of a permutation to a slice.
///
/// For a permutation p, this moves an element of the slice at position i to the position p(i).
///
/// Panics when the permutation's support is out of bounds.
impl<T> LeftAction<[T], Vec<bool>> for Perm {
    fn left_apply_to_with_scratch(&self, vec: &mut [T], scratch: &mut Vec<bool>) {
        assert!(vec.len() >= self.length);

        let mut cycles = self.cycles_with_scratch(replace(scratch, vec![]));

        while let Some(mut cycle) = cycles.next() {
            let mut prev = cycle.next().unwrap();
            for current in cycle {
                vec.swap(prev as usize, current as usize);
                prev = current;
            }
        }

        *scratch = cycles.into_scratch();
    }
}

/// Composition of a permutation on the left.
///
/// This is implemented via permutation of a slice's elements. Unlike composition on the right, this
/// requires scratch space and is likely less efficient.
impl LeftAction<Perm, Vec<bool>> for Perm {
    fn left_apply_to_with_scratch(&self, perm: &mut Perm, scratch: &mut Vec<bool>) {
        perm.extend_to(self.length);
        self.left_apply_to_with_scratch(&mut perm.perm[..], scratch);
    }
}

impl fmt::Display for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_with_scratch(f, &mut Default::default())
    }
}

impl fmt::Debug for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_with_scratch(f, &mut Default::default())
    }
}

impl PartialEq for Perm {
    fn eq(&self, other: &Perm) -> bool {
        self.perm_slice() == other.perm_slice()
    }
}

impl Eq for Perm {}

/// Iterator over the elements of a permutation's cycle.
#[derive(Clone)]
pub struct Cycle<'a> {
    perm: &'a Perm,
    pos: Option<El>,
    start: El,
}

impl<'a> Iterator for Cycle<'a> {
    type Item = El;

    fn next(&mut self) -> Option<El> {
        self.pos.map(|pos| {
            let next = self.perm.left_apply(pos);
            self.pos = if next == self.start { None } else { Some(next) };

            pos
        })
    }
}

impl<'a> fmt::Display for Cycle<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for el in self.clone() {
            f.write_str(if first { "(" } else { " " })?;
            first = false;
            fmt::Display::fmt(&el, f)?;
        }
        f.write_str(if first { "()" } else { ")" })
    }
}

impl<'a> fmt::Debug for Cycle<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Iterator over the cycles of a permutation.
#[derive(Clone)]
pub struct Cycles<'a> {
    perm: &'a Perm,
    seen: Vec<bool>,
    pos: El,
}

impl<'a> Cycles<'a> {
    /// Recover the scratch space needed for efficient iteration over the cycles of a permutation.
    fn into_scratch(self) -> Vec<bool> {
        self.seen
    }
}

impl<'a> Iterator for Cycles<'a> {
    type Item = Cycle<'a>;

    fn next(&mut self) -> Option<Cycle<'a>> {
        loop {
            // We can't see a cycle for the first time on the last element, so we can stop one early
            // and avoid a potential overflow
            if self.pos as usize >= self.perm.perm.len() {
                return None;
            } else if self.seen[self.pos as usize] || self.perm.left_apply(self.pos) == self.pos {
                self.pos += 1;
            } else {
                let cycle = self.perm.cycle_at(self.pos);
                for el in cycle.clone() {
                    self.seen[el as usize] = true;
                }
                return Some(cycle);
            }
        }
    }
}

pub struct Power<'a, E> {
    pub base: &'a Perm,
    pub exponent: E,
}

impl<'a, E> AssignValue<Perm, Perm> for Power<'a, E>
where
    E: Integer + ToPrimitive + FromPrimitive,
{
    fn assign_to_with_scratch(self, target: &mut Perm, scratch: &mut Perm) {
        let Power {
            base: perm,
            exponent: mut exp,
        } = self;

        let neg = exp < E::zero();

        let (target, scratch) = if neg {
            // We swap the roles of target and scratch so we don't need to swap when doing the final
            // inversion
            exp = E::zero() - exp;
            (scratch, target)
        } else {
            (target, scratch)
        };

        match exp.to_usize() {
            Some(0) => target.clone_from(&Perm::new()),
            Some(1) => target.clone_from(perm),
            Some(2) => target.assign(perm.square()),
            Some(3) => {
                target.assign(perm.square());
                perm.right_apply_to(target);
            }
            _ => {
                let odd = exp.is_odd();
                let half_exp = exp / E::from_usize(2).unwrap();

                scratch.assign_with_scratch(perm.pow(half_exp), target);
                target.assign(scratch.square());

                if odd {
                    perm.right_apply_to(target);
                }
            }
        }

        if neg {
            // scratch and target are swapped here
            scratch.assign(target.inverse());
        }
    }

    fn get_with_scratch(self, scratch: &mut Perm) -> Perm {
        let mut result = Perm::new();
        self.assign_to_with_scratch(&mut result, scratch);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::{prelude::*, *};

    fn random_perm<S>(size: S) -> impl Strategy<Value = Perm>
    where
        S: Strategy<Value = El>,
    {
        size.prop_map(|v| (0..v).collect::<Vec<_>>())
            .prop_shuffle()
            .prop_map(|vec| Perm::from_vec(vec).unwrap())
    }

    #[test]
    fn fmt_identity() {
        assert_eq!(format!("{}", Perm::new()), "()");
        assert_eq!(format!("{:?}", Perm::new()), "()");
    }

    #[test]
    fn fmt_perms() {
        assert_eq!(
            format!("{}", Perm::from_vec(vec![4, 1, 5, 2, 3, 0]).unwrap()),
            "(0 4 3 2 5)"
        );
        assert_eq!(
            format!("{:?}", Perm::from_vec(vec![2, 3, 1, 0, 5, 4]).unwrap()),
            "(0 2 1 3)(4 5)"
        );
    }

    #[test]
    fn composition_order() {
        let a = Perm::from_vec(vec![1, 0]).unwrap();
        let b = Perm::from_vec(vec![2, 3, 0, 1]).unwrap();

        let b_a = Perm::from_vec(vec![2, 3, 1, 0]).unwrap();
        let a_b = Perm::from_vec(vec![3, 2, 0, 1]).unwrap();

        assert_eq!(a.right_apply(b.clone()), b_a);
        assert_eq!(b.right_apply(a.clone()), a_b);

        assert_eq!(a.left_apply(b.clone()), a_b);
        assert_eq!(b.left_apply(a.clone()), b_a);
    }

    proptest! {
        #[test]
        fn from_vec_ok(v in (0..1000u32).prop_map(|v| (0..v).collect::<Vec<_>>()).prop_shuffle()) {
            prop_assert_eq!(v.clone(), Vec::from(Perm::from_vec(v.clone()).unwrap()));
        }

        #[test]
        fn from_vec_oob(
            mut v in (100..1000u32).prop_map(|v| (0..v).collect::<Vec<_>>()).prop_shuffle(),
            a in (1..100usize)
        ) {
            v.truncate(v.len() - a);
            prop_assume!(v.iter().any(|&x| x as usize >= v.len()));
            prop_assert!(Perm::from_vec(v).is_none())
        }

        #[test]
        fn from_vec_not_injective(
            mut v in prop::collection::vec(0..1000u32, 0..1000)
        ) {
            let n = v.len() as El;
            for el in v.iter_mut() {
                *el %= n;
            }
            let mut v2 = v.clone();
            v2.sort();
            v2.dedup();
            prop_assume!(v2.len() < v.len());
            prop_assert!(Perm::from_vec(v).is_none())
        }

        #[test]
        fn roundtrip_cycles(
            perm in random_perm(0..1000u32)
        ) {
            let mut perm2 = Perm::new();

            for mut cycle in perm.cycles() {
                let mut prev = cycle.next().unwrap();
                for current in cycle {
                    perm2.right_transpose(current, prev);
                    prev = current;
                }
            }

            assert_eq!(perm2, perm);
        }

        #[test]
        fn invert_by_reversing_cycles(
            perm in random_perm(0..1000u32)
        ) {
            let mut perm2 = Perm::new();

            for mut cycle in perm.cycles() {
                let mut prev = cycle.next().unwrap();
                for current in cycle.collect::<Vec<_>>().into_iter().rev() {
                    perm2.right_transpose(current, prev);
                    prev = current;
                }
            }

            assert_eq!(perm2, perm.inverse().get());
        }


        #[test]
        fn squaring_cyclewise(
            perm in random_perm(0..1000u32)
        ) {
            let mut perm2 = Perm::new();

            for cycle in perm.cycles() {
                for _ in 0..2 {
                    let mut cycle = cycle.clone();
                    let mut prev = cycle.next().unwrap();
                    for current in cycle.collect::<Vec<_>>().into_iter() {
                        perm2.right_transpose(current, prev);
                        prev = current;
                    }
                }
            }

            assert_eq!(perm2, perm.square().get());
        }

        #[test]
        fn adding_exponents(
            perm in random_perm(0..1000u32),
            a in 0..1_000_000usize,
            b in 0..1_000_000usize,
        ) {
            let perm_a = perm.pow(a).get();
            let perm_b = perm.pow(b).get();

            let combined = perm_a.right_apply(perm_b);

            let single = perm.pow(a + b).get();

            assert_eq!(combined, single);
        }

         #[test]
        fn adding_signed_exponents(
            perm in random_perm(0..1000u32),
            a in -1_000_000..1_000_000isize,
            b in -1_000_000..1_000_000isize,
        ) {
            let perm_a = perm.pow(a).get();
            let perm_b = perm.pow(b).get();

            let combined = perm_a.right_apply(perm_b);

            let single = perm.pow(a + b).get();

            assert_eq!(combined, single);
        }

        fn left_right_matches(
            perm_a in random_perm(0..1000u32),
            perm_b in random_perm(0..1000u32),
        ) {
            let combined_1 = perm_a.left_apply(perm_b.clone());
            let combined_2 = perm_b.right_apply(perm_a);

            assert_eq!(combined_1, combined_2);
        }
    }
}
