//! This crate provides a type registry that is capable of storing and providing back information about
//! historic Substrate based types (ie those that are handed back in pre-V14 metadata).

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
