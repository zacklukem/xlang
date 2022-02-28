//! Interning arena
//!
//! Where the interns go to fight for their lives
//!
//! Stores a type in the heap and ensures that the value is only stored once in
//! memory

use std::cell::RefCell;
use std::collections::HashSet;
use std::hash::Hash;

#[derive(Debug)]
pub struct Arena<T> {
    data: RefCell<HashSet<Box<T>>>,
}

impl<'a, T> Arena<T>
where
    T: Hash + Eq,
{
    pub fn new() -> Arena<T> {
        Arena {
            data: RefCell::new(HashSet::new()),
        }
    }

    /// Intern a value
    pub fn int(&self, val: T) -> Int<'a, T> {
        if let Some(val) = self.data.borrow().get(&val) {
            unsafe {
                let v = val.as_ref() as *const T;
                return Int(&*v);
            }
        }
        unsafe {
            let b = Box::new(val);
            let p = b.as_ref() as *const T;
            self.data.borrow_mut().insert(b);
            Int(&*p)
        }
    }
}

impl<'a, T> Default for Arena<T>
where
    T: Hash + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

/// Must use an arena to construct.  In type context, use TyCtx::int to construct
#[derive(Debug)]
pub struct Int<'a, T>(pub &'a T);

impl<'a, T> Copy for Int<'a, T> {}

impl<'a, T> Clone for Int<'a, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> std::ops::Deref for Int<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.0
    }
}

impl<'a, T> std::cmp::PartialEq for Int<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl<'a, T> std::cmp::Eq for Int<'a, T> {}

impl<'a, T> std::hash::Hash for Int<'a, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state)
    }
}

impl<'a, T> std::fmt::Display for Int<'a, T>
where
    T: std::fmt::Display + Hash + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
