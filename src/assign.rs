//! Traits enabling resource reuse for overwriting assignments.
use std::marker::PhantomData;

/// A computation whose result can be assigned to a value of type `T`.
///
/// Overwriting an existing value using [`Assign::assign`] allows reuse of existing resources (e.g.
/// allocations).
pub trait AssignValue<T>: Sized
where
    T: ?Sized,
{
    /// Type of scratch space needed to perform assignment.
    type Scratch: Default;

    /// Assign the result to a target.
    ///
    /// Using [`Assign::assign`] instead allows for the same source code order as for a plain
    /// assignment.
    fn assign_to(self, target: &mut T) {
        self.assign_to_with_scratch(target, &mut Self::Scratch::default());
    }

    /// Assign the result to a target. Use existing scratch space.
    ///
    /// Using [`Assign::assign_with_scratch`] instead allows for the same source code order as for a
    /// plain assignment.
    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut Self::Scratch);

    /// Return the result as a new value.
    fn get(self) -> T
    where
        T: Sized,
    {
        self.get_with_scratch(&mut Self::Scratch::default())
    }

    /// Return the result as a new value. Use existing scratch space.
    fn get_with_scratch(self, scratch: &mut Self::Scratch) -> T
    where
        T: Sized;
}

/// Create an assignable computation from a closure taking a mutable reference to the target and a
/// mutable reference to a scratch space.
pub struct AssignFnScratch<F, S>(pub F, pub PhantomData<FnOnce(&mut S)>);

impl<T, F, S> AssignValue<T> for AssignFnScratch<F, S>
where
    F: FnOnce(&mut T, &mut S),
    S: Default,
    T: Default,
{
    type Scratch = S;

    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut Self::Scratch) {
        self.0(target, scratch);
    }

    fn get_with_scratch(self, scratch: &mut Self::Scratch) -> T {
        let mut result = T::default();
        result.assign_with_scratch(self, scratch);
        result
    }
}

/// Create an assignable computation from a closure taking a mutable reference to the target.
pub struct AssignFn<F>(pub F);

impl<T, F> AssignValue<T> for AssignFn<F>
where
    F: FnOnce(&mut T),
    T: Default,
{
    type Scratch = ();

    fn assign_to_with_scratch(self, target: &mut T, _scratch: &mut ()) {
        self.0(target);
    }

    fn get_with_scratch(self, scratch: &mut ()) -> T {
        let mut result = T::default();
        result.assign_with_scratch(self, scratch);
        result
    }
}

/// Create an assignable computation from a closure producing a value and a mutable reference to a
/// scratch space.
///
/// This doesn't allow for resource reuse. It only allows to optionally provide existing scratch
/// space.
pub struct ProduceFnScratch<F, S>(pub F, pub PhantomData<FnOnce(&mut S)>);

impl<T, S, F> AssignValue<T> for ProduceFnScratch<F, S>
where
    F: FnOnce(&mut S) -> T,
    S: Default,
{
    type Scratch = S;

    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut Self::Scratch) {
        *target = self.0(scratch);
    }

    fn get_with_scratch(self, scratch: &mut Self::Scratch) -> T {
        self.0(scratch)
    }
}

/// Provide an `assign` methods on targets of [`AssignValue`].
pub trait Assign {
    fn assign<T>(&mut self, value: T)
    where
        T: AssignValue<Self>,
    {
        value.assign_to_with_scratch(self, &mut T::Scratch::default());
    }

    fn assign_with_scratch<T>(&mut self, value: T, scratch: &mut T::Scratch)
    where
        T: AssignValue<Self>,
    {
        value.assign_to_with_scratch(self, scratch);
    }
}

impl<T> Assign for T {}
