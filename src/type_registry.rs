//! This module provides a [`TypeRegistry`], which can be used to store and resolve
//! type information for types based on their names.

use std::collections::HashMap;
use crate::type_desc::TypeDesc;
use crate::type_name::TypeName;
use scale_type_resolver::{TypeResolver,ResolvedTypeVisitor};

/// An error resolving types.
#[derive(Debug,derive_more::Display)]
pub enum TypeRegistryError {

}

/// A type registry.
pub struct TypeRegistry {
    // A hash from the name of a type (like `Vec` or `usize`) to a description
    // of the shape of the type (which may involve generic params or just be
    // concrete types or aliases to other types).
    types: HashMap<String, TypeDesc>,
}

impl TypeResolver for TypeRegistry {
    type TypeId = TypeName;
    type Error = TypeRegistryError;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: &Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        todo!()
    }
}