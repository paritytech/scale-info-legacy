//! This module provides a struct, [`TypeDescription`]. This struct defines a single type that can
//! be inserted into the [`crate::type_registry::TypeRegistry`].

use crate::type_name::{TypeName, TypeNameDef};
use crate::type_shape::TypeShape;
use alloc::borrow::ToOwned;
use alloc::string::String;
use smallvec::SmallVec;

/// A type to insert into the registry. A single method is exposed, [`TypeDescription::new`],
/// which takes a type name (including any generics) like `"Vec<T>"` or `"Foo"` along with a
/// [`TypeShape`] which defines how this type should be SCALE encoded/decoded.
///
/// See [`crate::TypeRegistry::insert()`] for a full example.
///
/// # Example
///
/// ```rust
/// use scale_info_legacy::{ TypeDescription, TypeShape, TypeName };
///
/// // Describe a type (this is how a Vec is described). Note that you should
/// // use the generic parameters where necessary in the description.
/// let vec_description = TypeDescription::new(
///     "Vec<T>",
///     TypeShape::SequenceOf(TypeName::parse_unwrap("T"))
/// ).unwrap();
/// ```
pub struct TypeDescription {
    /// The name of the type.
    name: String,
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    /// A description of the shape of the type.
    shape: TypeShape,
}

impl TypeDescription {
    /// Create a [`Ty`] by providing a name like "Bar" or "Foo<A, B>" and a description of
    /// the shape of the type with this name.
    pub fn new(name_with_params: impl AsRef<str>, shape: TypeShape) -> Result<Self, ParseError> {
        // The name we are looking for is just a restricted form of a ty_name, so we
        // will just borrow that parsing logic and then check that we get the expected shape back:
        let ty_name =
            TypeName::parse(name_with_params.as_ref()).map_err(|_| ParseError::InvalidTyName)?;

        // We only accept named types like Foo<A, B> or path::to::Bar.
        let TypeNameDef::Named(named_ty) = ty_name.def() else {
            return Err(ParseError::ExpectingNamedType);
        };

        let name = named_ty.name().to_owned();
        let params: Result<_, _> = named_ty
            .param_defs()
            .map(|param| {
                // Params must be simple names and not array/tuples.
                let TypeNameDef::Named(name) = param else {
                    return Err(ParseError::ExpectingNamedParam);
                };
                // Param names must be capitalized because they represent generics.
                if name.name().starts_with(|c: char| c.is_lowercase()) {
                    return Err(ParseError::ExpectingUppercaseParams);
                }
                Ok(name.name().to_owned())
            })
            .collect();

        Ok(TypeDescription { name, params: params?, shape })
    }

    /// Break this into parts to be inserted.
    pub(crate) fn into_parts(self) -> (String, SmallVec<[String; 4]>, TypeShape) {
        let TypeDescription { name, params, shape } = self;
        (name, params, shape)
    }
}

/// An error creating some type [`Ty`].
#[allow(missing_docs)]
#[derive(Debug, derive_more::Display)]
pub enum ParseError {
    #[display(
        fmt = "Failed to parse the type name. Expected something like 'Foo' or 'Bar<A, B>'."
    )]
    InvalidTyName,
    #[display(
        fmt = "Expected something like 'Foo' or 'Bar<A, B>' but got an array or tuple type."
    )]
    ExpectingNamedType,
    #[display(
        fmt = "Expected the generic params to be names like 'A' or 'B', not arrays or tuples."
    )]
    ExpectingNamedParam,
    #[display(fmt = "Expected the generic params to be capitalized.")]
    ExpectingUppercaseParams,
}
