//! This module provides a [`TypeRegistry`], which can be used to store and resolve
//! type information for types based on their names.

use std::collections::HashMap;
use std::iter::ExactSizeIterator;
use smallvec::SmallVec;
use crate::type_desc::{TypeDesc, VariantDesc };
use crate::type_name::{ TypeName, TypeNameDef };
use scale_type_resolver::{TypeResolver,ResolvedTypeVisitor,Field,Variant};

/// An error resolving types.
#[allow(missing_docs)]
#[derive(Debug,derive_more::Display)]
pub enum TypeRegistryError {
    #[display(fmt = "Type '{_0}' not found")]
    TypeNotFound(String),
    #[display(fmt = "Wrong number of params provided for {type_name}: expected {expected_params} but got {provided_params}")]
    TypeParamsMismatch {
        type_name: String,
        expected_params: usize,
        provided_params: usize,
    }
}

/// A type registry.
pub struct TypeRegistry {
    // A hash from the name of a type (like `Vec` or `usize`) to a description
    // of the shape of the type (which may involve generic params or just be
    // concrete types or aliases to other types).
    types: HashMap<String, TypeInfo>,
}

struct TypeInfo {
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    // A description of the shape of the type.
    desc: TypeDesc
}

impl <'a> TypeResolver for TypeRegistry {
    type TypeId<'id> = TypeName;
    type Error = TypeRegistryError;

    fn resolve_type<'this,'id, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId<'id>>>(
        &'this self,
        type_id: Self::TypeId<'id>,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match type_id.def() {
            TypeNameDef::Named(ty) => {
                let Some(type_info) = self.types.get(ty.name()) else {
                    return Err(TypeRegistryError::TypeNotFound(ty.name().to_owned()))
                };

                let num_input_params = ty.param_defs().count();
                let num_expected_params = type_info.params.len();

                // Complain if you try asking for a type and don't provide the expected number
                // of parameters in place of that types generics.
                if num_input_params != num_expected_params {
                    return Err(TypeRegistryError::TypeParamsMismatch {
                        type_name: ty.name().to_owned(),
                        expected_params: num_expected_params,
                        provided_params: num_input_params,
                    })
                }

                // Build a mapping from generic ident to the concrete type def we've been given.
                // We use this to update generic type names like Vec<T> into concrete ones that the
                // user can access in the registry, like Vec<u32>,
                let param_mapping: SmallVec<[(&str, TypeNameDef<'_>); 4]> = type_info.params
                    .iter()
                    .map(|ident| ident.as_str())
                    .zip(ty.param_defs())
                    .collect();

                // Visit the provided visitor with the relevant details.
                match &type_info.desc {
                    TypeDesc::StructOf(fields) => {
                        let fields_iter = fields
                            .iter()
                            .map(|field| Field {
                                name: Some(&field.name),
                                id: apply_param_mapping(field.value.clone(), &param_mapping),
                            });
                        Ok(visitor.visit_composite(fields_iter))
                    },
                    TypeDesc::EnumOf(variants) => {
                        let variants_iter = variants
                            .iter()
                            .map(|var| Variant {
                                index: var.index,
                                name: &var.name,
                                fields: match &var.value {
                                    VariantDesc::StructOf(fields) => {
                                        let field_iter = fields
                                            .iter()
                                            .map(|field| Field {
                                                name: Some(&field.name),
                                                // TODO: Why does stuff handed to eg visit_variant need lifetime of `'resolver`? Can it be more temporary? Would mean values can't
                                                // contain items borrowed from the registry, but would also mean we could have temporary stuff like param_mapping captures by the
                                                // iterator. Otherwise we'll have to Wrap it into an Rc/Arc to share it or something.
                                                id: apply_param_mapping(field.value.clone(), &param_mapping),
                                            });
                                        Either::A(field_iter)
                                    },
                                    VariantDesc::TupleOf(fields) => {
                                        let field_iter = fields
                                            .iter()
                                            .map(|ty| Field {
                                                name: None,
                                                id: apply_param_mapping(ty.clone(), &param_mapping),
                                            });
                                        Either::B(field_iter)
                                    }
                                }
                            });
                        Ok(visitor.visit_variant(variants_iter))
                    },
                    TypeDesc::Sequenceof(_) => todo!(),
                    TypeDesc::ArrayOf(_, _) => todo!(),
                    TypeDesc::TupleOf(_) => todo!(),
                    TypeDesc::BitSequence(_, _) => todo!(),
                    TypeDesc::Compact(_) => todo!(),
                    TypeDesc::Primitive(_) => todo!(),
                    TypeDesc::AliasOf(_) => todo!(),
                    // TypeDesc::Generic(_) => todo!(),
                }
            },
            TypeNameDef::Unnamed(ty) => {
                todo!()
            },
            TypeNameDef::Array(ty) => {
                todo!()
            },
        }
    }
}

/// Takes a TypeName and a mapping from generic ident to new defs, and returns a new TypeName where
/// said generic params are replaced with concrete types.
fn apply_param_mapping(ty: TypeName, param_mapping: &SmallVec<[(&str, TypeNameDef<'_>); 4]>) -> TypeName {
    param_mapping.iter().fold(ty, |ty, (ident, def)| ty.with_substitution(ident, *def))
}

enum Either<A,B> {
    A(A),
    B(B)
}

impl <Item, A: Iterator<Item=Item>, B: Iterator<Item=Item>> Iterator for Either<A, B> {
    type Item = Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::A(a) => a.next(),
            Either::B(b) => b.next()
        }
    }
}
impl <Item, A: ExactSizeIterator<Item=Item>, B: ExactSizeIterator<Item=Item>> ExactSizeIterator for Either<A, B> {
    fn len(&self) -> usize {
        match self {
            Either::A(a) => a.len(),
            Either::B(b) => b.len(),
        }
    }
}

/*
types: {
    "Vec" => TypeInfo {
        params: ["T"]
        desc: SequenceOf("T")
    },

    "Foo" => TypeInfo {
        params: ["A", "B"],
        desc: StructOf {[
            "a": "Vec<A>",
            "b": "u32",
            "c": "(A, B)"
        ]}
    },

    "u32": Primitive::u32,

    "Bar": TupleOf[ bool, String ]
}

Foo<Bar<u32>> => ERROR: Foo has 2 params but only one provided.

Foo<Bar<u32>, Vec<String>>:

  Foo has 2 params A, B so:
  param_mappings: { A => "Bar<u32>", B => "Vec<String>" }

  Foo is struct so we need to return field names and TypeIds. Return:
  - "a": "Vec<Bar<u32>>",
  - "b": "u32",
  - "c": "(Bar<u32>, Vec<String>)"

  so we find types in the TypeName that match our generic params eg A, B and create a new
  TypeName which substitutes those for some concrete types, to prepare for the next lookup.

*/