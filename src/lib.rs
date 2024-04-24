//! This crate provides a type registry that is capable of storing and providing back information about
//! historic Substrate based types (ie those that are handed back in pre-V14 metadata).

#![deny(missing_docs)]

pub mod ty;
pub mod ty_name;
pub mod ty_desc;
pub mod type_registry;
