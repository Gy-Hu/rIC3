use std::{
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
    rc::Rc,
    sync::Arc,
};

macro_rules! define_rc_wrapper {
    ($wrapper:ident, $inner:ident) => {
        #[derive(Debug, Default)]
        pub struct $wrapper<T> {
            inner: $inner<T>,
        }

        impl<T> $wrapper<T> {
            #[inline]
            pub fn new(v: T) -> Self {
                Self {
                    inner: $inner::new(v),
                }
            }

            #[inline]
            pub fn as_ptr(&self) -> *const T {
                $inner::as_ptr(&self.inner)
            }

            /// # Safety
            #[inline]
            pub unsafe fn from_ptr(p: *const T) -> Self {
                Self {
                    inner: unsafe { $inner::from_raw(p) },
                }
            }

            #[inline]
            pub fn count(&self) -> usize {
                $inner::strong_count(&self.inner)
            }

            #[inline]
            pub fn increment_count(&self) {
                unsafe { $inner::increment_strong_count(self.as_ptr()) }
            }

            /// # Safety
            #[inline]
            #[allow(clippy::mut_from_ref)]
            pub unsafe fn get_mut_from_unmut(&self) -> &mut T {
                unsafe { &mut *(self.as_ptr() as *mut T) }
            }
        }

        impl<T> Deref for $wrapper<T> {
            type Target = T;

            #[inline]
            fn deref(&self) -> &Self::Target {
                self.inner.deref()
            }
        }

        impl<T> DerefMut for $wrapper<T> {
            #[inline]
            fn deref_mut(&mut self) -> &mut Self::Target {
                unsafe { $inner::get_mut_unchecked(&mut self.inner) }
            }
        }

        impl<T> PartialEq for $wrapper<T> {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                $inner::as_ptr(&self.inner) == $inner::as_ptr(&other.inner)
            }
        }

        impl<T> Eq for $wrapper<T> {}

        impl<T> Hash for $wrapper<T> {
            #[inline]
            fn hash<H: Hasher>(&self, state: &mut H) {
                $inner::as_ptr(&self.inner).hash(state);
            }
        }

        unsafe impl<T> Sync for $wrapper<T> {}

        impl<T> Clone for $wrapper<T> {
            #[inline]
            fn clone(&self) -> Self {
                Self {
                    inner: self.inner.clone(),
                }
            }
        }
    };
}

define_rc_wrapper!(Grc, Rc);
define_rc_wrapper!(Garc, Arc);
