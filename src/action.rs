//! Group actions.

/// Left action on `T`.
///
/// Elements of implementing types act on `T` values on the left.
pub trait LeftAction<T>
where
    T: ?Sized,
{
    /// Type of scratch space needed to perform group action.
    type Scratch: Default;

    /// Act on a value on the left.
    fn left_apply(&self, value: T) -> T
    where
        T: Sized,
    {
        self.left_apply_with_scratch(value, &mut Self::Scratch::default())
    }

    /// Act on a value on the left. Use existing scratch space.
    fn left_apply_with_scratch(&self, mut value: T, scratch: &mut Self::Scratch) -> T
    where
        T: Sized,
    {
        self.left_apply_to_with_scratch(&mut value, scratch);
        value
    }

    /// Act on a value, in place, on the left.
    fn left_apply_to(&self, value: &mut T) {
        self.left_apply_to_with_scratch(value, &mut Self::Scratch::default())
    }

    /// Act on a value, in place, on the left. Use existing scratch space.
    fn left_apply_to_with_scratch(&self, value: &mut T, scratch: &mut Self::Scratch);
}

/// Right action on `T`.
///
/// Elements of implementing types act on `T` values on the right.
pub trait RightAction<T>
where
    T: ?Sized,
{
    /// Type of scratch space needed to perform group action.
    type Scratch: Default;

    /// Act on a value on the right.
    fn right_apply(&self, value: T) -> T
    where
        T: Sized,
    {
        self.right_apply_with_scratch(value, &mut Self::Scratch::default())
    }

    /// Act on a value on the right. Use existing scratch space.
    fn right_apply_with_scratch(&self, mut value: T, scratch: &mut Self::Scratch) -> T
    where
        T: Sized,
    {
        self.right_apply_to_with_scratch(&mut value, scratch);
        value
    }

    /// Act on a value, in place, on the right.
    fn right_apply_to(&self, value: &mut T) {
        self.right_apply_to_with_scratch(value, &mut Self::Scratch::default())
    }

    /// Act on a value, in place, on the right. Use existing scratch space.
    fn right_apply_to_with_scratch(&self, value: &mut T, scratch: &mut Self::Scratch);
}
