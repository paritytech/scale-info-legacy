//! This crate provides a [`TypeRegistry`] that is capable of storing and providing back information about
//! historic Substrate based types (ie those that are handed back in pre-V14 metadata).
//!
//! See [`TypeRegistry::insert()`] to learn how to add types to the registry, and [`TypeRegistry::resolve_type()`]
//! to learn how to then resolve type information using the registry.

#![no_std]
#![deny(missing_docs)]

extern crate alloc;

pub mod type_description;
pub mod type_name;
pub mod type_registry;
pub mod type_shape;

// Export the main types here for ease of use:
pub use {
    type_description::TypeDescription, type_name::TypeName, type_registry::TypeRegistry,
    type_shape::TypeShape,
};
