//! A permutation group library
//!
//! This crate provides data structures and algorithms for working with permutations and permutation
//! groups.
//!
//! This is currently an early work in progress.
//!
pub mod assign;
pub mod action;
pub mod perm;

/// Set element.
///
/// Set elements are represented by non-negative integers (`u32`).
pub type El = u32;

