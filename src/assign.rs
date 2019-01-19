//! Traits enabling resource reuse for overwriting assignments.

/// A computation whose result can be assigned to a value of type `T`. (Using `S` as scratch space.)
///
/// Overwriting an existing value using [`Assign::assign`] allows reuse of existing resources (e.g.
/// allocations).
pub trait AssignValue<T, S = ()>: Sized
where
    S: ?Sized,
    T: ?Sized,
{
    /// Assign the result to a target.
    ///
    /// Using [`Assign::assign`] instead allows for the same source code order as for a plain
    /// assignment.
    fn assign_to(self, target: &mut T)
    where
        S: Default,
    {
        self.assign_to_with_scratch(target, &mut S::default());
    }

    /// Assign the result to a target. Use existing scratch space.
    ///
    /// Using [`Assign::assign_with_scratch`] instead allows for the same source code order as for a
    /// plain assignment.
    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut S);

    /// Return the result as a new value.
    fn get(self) -> T
    where
        T: Sized,
        S: Default,
    {
        self.get_with_scratch(&mut S::default())
    }

    /// Return the result as a new value. Use existing scratch space.
    fn get_with_scratch(self, scratch: &mut S) -> T
    where
        T: Sized;
}

/// Create an assignable computation from a closure taking a mutable reference to the target and a
/// mutable reference to a scratch space.
pub struct AssignFnScratch<F>(pub F);

impl<T, S, F> AssignValue<T, S> for AssignFnScratch<F>
where
    F: FnOnce(&mut T, &mut S),
    T: Default,
{
    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut S) {
        self.0(target, scratch);
    }

    fn get_with_scratch(self, scratch: &mut S) -> T {
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
pub struct ProduceFnScratch<F>(pub F);

impl<T, S, F> AssignValue<T, S> for ProduceFnScratch<F>
where
    F: FnOnce(&mut S) -> T,
{
    fn assign_to_with_scratch(self, target: &mut T, scratch: &mut S) {
        *target = self.0(scratch);
    }

    fn get_with_scratch(self, scratch: &mut S) -> T {
        self.0(scratch)
    }
}

/// Provide an `assign` methods on targets of [`AssignValue`].
pub trait Assign {
    fn assign<T, S>(&mut self, value: T)
    where
        T: AssignValue<Self, S>,
        S: Default,
    {
        value.assign_to_with_scratch(self, &mut S::default());
    }

    fn assign_with_scratch<T, S>(&mut self, value: T, scratch: &mut S)
    where
        T: AssignValue<Self, S>,
    {
        value.assign_to_with_scratch(self, scratch);
    }
}

impl<T> Assign for T {}
