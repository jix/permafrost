//! Group actions.

/// Left action on `T`. (Using `S` as scratch space.)
///
/// Elements of implementing types act on `T` values on the left.
pub trait LeftAction<T, S=()>
where
    T: ?Sized,
{
    /// Act on a value on the left.
    fn left_apply(&self, value: T) -> T
    where
        S: Default,
        T: Sized,
    {
        self.left_apply_with_scratch(value, &mut S::default())
    }

    /// Act on a value on the left. Use existing scratch space.
    fn left_apply_with_scratch(&self, mut value: T, scratch: &mut S) -> T
    where
        T: Sized,
    {
        self.left_apply_to_with_scratch(&mut value, scratch);
        value
    }

    /// Act on a value, in place, on the left.
    fn left_apply_to(&self, value: &mut T)
    where
        S: Default,
    {
        self.left_apply_to_with_scratch(value, &mut S::default())
    }

    /// Act on a value, in place, on the left. Use existing scratch space.
    fn left_apply_to_with_scratch(&self, value: &mut T, scratch: &mut S);
}

/// Right action on `T`. (Using `S` as scratch space.)
///
/// Elements of implementing types act on `T` values on the right.
pub trait RightAction<T, S=()>
where
    T: ?Sized,
{
    /// Act on a value on the right.
    fn right_apply(&self, value: T) -> T
    where
        S: Default,
        T: Sized,
    {
        self.right_apply_with_scratch(value, &mut S::default())
    }

    /// Act on a value on the right. Use existing scratch space.
    fn right_apply_with_scratch(&self, mut value: T, scratch: &mut S) -> T
    where
        T: Sized,
    {
        self.right_apply_to_with_scratch(&mut value, scratch);
        value
    }

    /// Act on a value, in place, on the right.
    fn right_apply_to(&self, value: &mut T)
    where
        S: Default,
    {
        self.right_apply_to_with_scratch(value, &mut S::default())
    }

    /// Act on a value, in place, on the right. Use existing scratch space.
    fn right_apply_to_with_scratch(&self, value: &mut T, scratch: &mut S);
}
