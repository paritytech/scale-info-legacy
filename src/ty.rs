//! This module provides a struct, [`Ty`], to describe the name, generic params and shape of some type that you'd like to insert into the [`crate::type_registry::TypeRegistry`].

use smallvec::SmallVec;
use crate::ty_desc::Shape;
use crate::ty_name::{Name, NameDef};

/// A type to insert into the registry.
pub struct Ty {
    /// The name of the type.
    name: String,
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    /// A description of the shape of the type.
    shape: Shape,
}

impl Ty {
    /// Create a [`Ty`] by providing a name like "Bar" or "Foo<A, B>" and a description of
    /// the shape of the type with this name.
    pub fn new(name_with_params: impl AsRef<str>, shape: Shape) -> Result<Self, ParseError> {
        // The name we are looking for is just a restricted form of a ty_name, so we
        // will just borrow that parsing logic and then check that we get the expected shape back:
        let ty_name = Name::parse(name_with_params.as_ref())
            .map_err(|_| ParseError::InvalidTyName)?;

        // We only accept named types like Foo<A, B> or path::to::Bar.
        let NameDef::Named(named_ty) = ty_name.def() else {
            return Err(ParseError::ExpectingNamedType);
        };

        let name = named_ty.name().to_owned();
        let params: Result<_,_> = named_ty.param_defs().map(|param| {
            // Params must be simple names and not array/tuples.
            let NameDef::Named(name) = param else {
                return Err(ParseError::ExpectingNamedParam)
            };
            // Param names must be capitalized because they represent generics.
            if name.name().starts_with(|c: char| c.is_lowercase()) {
                return Err(ParseError::ExpectingUppercaseParams)
            }
            Ok(name.name().to_owned())
        }).collect();

        Ok(Ty { name, params: params?, shape })
    }

    /// Break this into parts to be inserted.
    pub(crate) fn into_parts(self) -> (String, SmallVec<[String; 4]>, Shape) {
        let Ty { name, params, shape } = self;
        (name, params, shape)
    }
}

/// An error creating some type [`Ty`].
#[allow(missing_docs)]
#[derive(Debug,derive_more::Display)]
pub enum ParseError {
    #[display(fmt = "Failed to parse the type name. Expected something like 'Foo' or 'Bar<A, B>'.")]
    InvalidTyName,
    #[display(fmt = "Expected something like 'Foo' or 'Bar<A, B>' but got an array or tuple type.")]
    ExpectingNamedType,
    #[display(fmt = "Expected the generic params to be names like 'A' or 'B', not arrays or tuples.")]
    ExpectingNamedParam,
    #[display(fmt = "Expected the generic params to be capitalized.")]
    ExpectingUppercaseParams,
}
