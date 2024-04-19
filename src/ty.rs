//! This module provides a struct, [`Ty`], to describe the name, generic params and shape of some type that you'd like to insert into the [`crate::type_registry::TypeRegistry`].

use smallvec::SmallVec;
use crate::ty_desc::TyDesc;

/// A type to insert into the registry.
pub struct Ty {
    /// The name of the type.
    name: String,
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    /// A description of the shape of the type.
    shape: TyDesc,
}

impl Ty {
    /// Create a [`Ty`] by providing a name like "Bar" or "Foo<A, B>" and a description of
    /// the shape of the type with this name.
    pub fn new(name_with_params: impl AsRef<str>, shape: TyDesc) -> Result<Self, TyError> {

    }

    /// Break this into parts to be inserted.
    pub(crate) fn into_parts(self) -> (String, SmallVec<[String; 4]>, TyDesc) {
        let Ty { name, params, shape } = self;
        (name, params, shape)
    }
}

/// An error creating some type [`Ty`].
#[allow(missing_docs)]
#[derive(Debug,derive_more::Display)]
pub enum TyError {

}