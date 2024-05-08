// Copyright (C) 2024 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-info-legacy crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This module provides a [`TypeRegistry`], which can be used to store and resolve
//! type information for types based on their names.

use crate::type_description::TypeDescription;
use crate::type_name::{self, TypeName, TypeNameDef};
use crate::type_shape::{self, Primitive, TypeShape, VariantDesc};
use alloc::borrow::ToOwned;
use alloc::string::String;
use alloc::vec;
use core::hash::Hash;
use core::iter::ExactSizeIterator;
use hashbrown::HashMap;
use scale_type_resolver::{
    BitsOrderFormat, BitsStoreFormat, Field, ResolvedTypeVisitor, TypeResolver, Variant,
};
use smallvec::SmallVec;

/// An error resolving types.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq, derive_more::Display)]
pub enum TypeRegistryResolveError {
    #[display(fmt = "'{_0}' is not a valid type name: {_1}")]
    TypeNameInvalid(String, type_name::ParseError),
    #[display(fmt = "Type '{_0}' not found")]
    TypeNotFound(String),
    #[display(
        fmt = "Wrong number of params provided for {type_name}: expected {expected_params} but got {provided_params}"
    )]
    TypeParamsMismatch { type_name: String, expected_params: usize, provided_params: usize },
    #[display(
        fmt = "Bitvecs must have an order type with the path bitvec::order::Msb0 or bitvec::order::Lsb0"
    )]
    UnexpectedBitOrderType,
    #[display(
        fmt = "Bitvecs must have a store type which resolves to a primitive u8, u16, u32 or u64 type."
    )]
    UnexpectedBitStoreType,
}

#[cfg(feature = "std")]
impl std::error::Error for TypeRegistryResolveError {}

/// An error when using `TypeRegistry::try_resolve_type()`. This returns the visitor if
/// the type wasn't found, allowing us to use it again with a different registry or whatever.
#[allow(missing_docs)]
#[derive(Debug, Clone, derive_more::Display)]
pub enum TypeRegistryTryResolveError<Visitor> {
    #[display(fmt = "Type '{name}' not found")]
    TypeNotFound { name: String, visitor: Visitor },
    #[display(fmt = "{_0}")]
    Other(TypeRegistryResolveError),
}

/// The type info stored in the registry against a given named type.
#[derive(Debug)]
struct TypeInfo {
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    // A description of the shape of the type.
    desc: TypeShape,
}

/// Key pointing at named types we've stored.
#[derive(Clone, Debug, PartialEq, Eq)]
struct TypeKey {
    pallet: Option<String>,
    name: String,
}

impl core::hash::Hash for TypeKey {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        hash_key(self.pallet.as_deref(), &self.name, state);
    }
}

fn hash_key<H: core::hash::Hasher>(pallet: Option<&str>, name: &str, state: &mut H) {
    pallet.hash(state);
    name.hash(state);
}

/// A type registry that stores a mapping from type names to a description of how to SCALE
/// encode/decode that type.
///
/// To insert a new type description, use [`TypeRegistry::insert()`]. To look up the shape
/// of a type, use [`TypeRegistry::resolve_type()`]. [`TypeRegistry`] implements
/// [`scale_type_resolver::TypeResolver`], which means that it can be used in conjunction with
/// the `scale-encode` crate to SCALE encode types, or the `scale-decode` crate to SCALE decode
/// bytes into some type.
pub struct TypeRegistry {
    // A hash from the name of a type (like `Vec` or `usize`) to a description
    // of the shape of the type (which may involve generic params or just be
    // concrete types or aliases to other types).
    types: HashMap<TypeKey, TypeInfo>,
}

impl TypeRegistry {
    /// Create a new and completely empty [`TypeRegistry`]. Most of the time you should
    /// start with [`TypeRegistry::basic()`] to get a registry pre-populated with built in
    /// rust types.
    pub fn empty() -> Self {
        TypeRegistry { types: HashMap::new() }
    }

    /// Create a new [`TypeRegistry`] that's pre-populated with built-in rust types.
    pub fn basic() -> Self {
        let mut registry = TypeRegistry::empty();

        let basic_types = [
            ("bool", TypeShape::Primitive(Primitive::Bool)),
            ("char", TypeShape::Primitive(Primitive::Char)),
            ("u8", TypeShape::Primitive(Primitive::U8)),
            ("u16", TypeShape::Primitive(Primitive::U16)),
            ("u32", TypeShape::Primitive(Primitive::U32)),
            ("u64", TypeShape::Primitive(Primitive::U64)),
            ("u128", TypeShape::Primitive(Primitive::U128)),
            ("u256", TypeShape::Primitive(Primitive::U256)),
            ("i8", TypeShape::Primitive(Primitive::I8)),
            ("i16", TypeShape::Primitive(Primitive::I16)),
            ("i32", TypeShape::Primitive(Primitive::I32)),
            ("i64", TypeShape::Primitive(Primitive::I64)),
            ("i128", TypeShape::Primitive(Primitive::I128)),
            ("i256", TypeShape::Primitive(Primitive::I256)),
            ("str", TypeShape::Primitive(Primitive::Str)),
            ("String", TypeShape::Primitive(Primitive::Str)),
            ("Box<T>", TypeShape::AliasOf(TypeName::parse("T").unwrap())),
            ("Arc<T>", TypeShape::AliasOf(TypeName::parse("T").unwrap())),
            ("Rc<T>", TypeShape::AliasOf(TypeName::parse("T").unwrap())),
            ("Cell<T>", TypeShape::AliasOf(TypeName::parse("T").unwrap())),
            ("RefCell<T>", TypeShape::AliasOf(TypeName::parse("T").unwrap())),
            ("Vec<T>", TypeShape::SequenceOf(TypeName::parse("T").unwrap())),
            ("LinkedList<T>", TypeShape::SequenceOf(TypeName::parse("T").unwrap())),
            ("VecDeque<T>", TypeShape::SequenceOf(TypeName::parse("T").unwrap())),
            ("BTreeMap<K,V>", TypeShape::SequenceOf(TypeName::parse("(K, V)").unwrap())),
            ("BTreeSet<V>", TypeShape::SequenceOf(TypeName::parse("V").unwrap())),
            ("BinaryHeap<V>", TypeShape::SequenceOf(TypeName::parse("V").unwrap())),
            ("Cow<T>", TypeShape::TupleOf(vec![TypeName::parse("T").unwrap()])),
            (
                "Option<T>",
                TypeShape::EnumOf(vec![
                    type_shape::Variant {
                        index: 0,
                        name: "None".to_owned(),
                        value: type_shape::VariantDesc::TupleOf(vec![]),
                    },
                    type_shape::Variant {
                        index: 1,
                        name: "Some".to_owned(),
                        value: type_shape::VariantDesc::TupleOf(
                            vec![TypeName::parse("T").unwrap()],
                        ),
                    },
                ]),
            ),
            (
                "Result<T,E>",
                TypeShape::EnumOf(vec![
                    type_shape::Variant {
                        index: 0,
                        name: "Ok".to_owned(),
                        value: type_shape::VariantDesc::TupleOf(
                            vec![TypeName::parse("T").unwrap()],
                        ),
                    },
                    type_shape::Variant {
                        index: 1,
                        name: "Err".to_owned(),
                        value: type_shape::VariantDesc::TupleOf(
                            vec![TypeName::parse("E").unwrap()],
                        ),
                    },
                ]),
            ),
            ("PhantomData", TypeShape::TupleOf(vec![])),
            // These exist just so that resolving bitvecs using these store types will work.
            ("bitvec::order::Lsb0", TypeShape::StructOf(vec![])),
            ("bitvec::order::Msb0", TypeShape::StructOf(vec![])),
            // So long as the store type is a suitable primitive and the order type one of the above, this will work out.
            (
                "bitvec::vec::BitVec<Store, Order>",
                TypeShape::BitSequence {
                    store: TypeName::parse("Store").unwrap(),
                    order: TypeName::parse("Order").unwrap(),
                },
            ),
            // Types seem to mostly use this alias to BitVec:
            (
                "BitVec<Store, Order>",
                TypeShape::AliasOf(TypeName::parse("bitvec::vec::BitVec<Store, Order>").unwrap()),
            ),
        ];

        for (name, desc) in basic_types {
            registry.insert(TypeDescription::new(name, desc).expect("basic type should be valid"));
        }

        registry
    }

    /// Insert a new type into the registry.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_info_legacy::{ TypeRegistry, TypeDescription, TypeShape, TypeName };
    ///
    /// // Describe a type:
    /// let desc = TypeDescription::new(
    ///     "Foo<T>",
    ///     TypeShape::SequenceOf(TypeName::parse("T").unwrap())
    /// ).unwrap();
    ///
    /// // Add a type description to our registry:
    /// let mut registry = TypeRegistry::empty();
    /// registry.insert(desc);
    /// ```
    pub fn insert(&mut self, ty: TypeDescription) {
        let (pallet, name, params, desc) = ty.into_parts();
        self.types.insert(TypeKey { pallet, name }, TypeInfo { desc, params });
    }

    /// Resolve some type information by providing a [`TypeName`], which is the
    /// concrete name of a type we want to know how to decode values for, and a
    /// `visitor` which will be called in order to describe how to decode it.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_info_legacy::{ TypeRegistry, TypeDescription, TypeShape, TypeName };
    /// use scale_type_resolver::visitor;
    ///
    /// // Name a type that you want to know how to encode/decode:
    /// let name = TypeName::parse("Vec<(bool, u32)>").unwrap();
    ///
    /// // Here we provide a dumb visitor (ie set of callbacks) which will return
    /// // true if the type we ask about is a sequence, and false otherwise.
    /// let my_visitor = visitor::new((), |_, _| false)
    ///     .visit_sequence(|_, _, _| true);
    ///
    /// // Query this name in our registry, passing our visitor:
    /// let mut registry = TypeRegistry::basic();
    /// let is_sequence = registry.resolve_type(name, my_visitor).unwrap();
    ///
    /// assert!(is_sequence);
    /// ```
    pub fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = TypeName>>(
        &'this self,
        type_id: TypeName,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryResolveError> {
        match self.try_resolve_type(type_id, visitor) {
            Err(TypeRegistryTryResolveError::TypeNotFound { visitor, .. }) => {
                Ok(visitor.visit_not_found())
            }
            Err(TypeRegistryTryResolveError::Other(e)) => Err(e),
            Ok(val) => Ok(val),
        }
    }

    /// Like [`TypeRegistry::resolve_type()`], but returns the visitor again if the type
    /// wasn't found (along with the name of the type we didn't find), rather than consuming
    /// the visitor by calling `.visit_not_found()` on it. This allows you to re-use the visitor,
    /// or just learn a little bit more about the failure.
    pub fn try_resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = TypeName>>(
        &'this self,
        type_id: TypeName,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryTryResolveError<V>> {
        // The pallet that our lookups will be performed within:
        let pallet = type_id.pallet();

        match type_id.def() {
            TypeNameDef::Named(ty) => {
                let Some((ty_key, type_info)) =
                    lookup(pallet, ty.name(), &self.types).or_else(|| {
                        if pallet.is_some() {
                            // We did a scoped lookup and found nothing, so now try without scope.
                            lookup(None, ty.name(), &self.types)
                        } else {
                            // We did an un-scoped lookup and found nothing, so give up!
                            None
                        }
                    })
                else {
                    return Err(TypeRegistryTryResolveError::TypeNotFound {
                        name: ty.name().to_owned(),
                        visitor,
                    });
                };

                let num_input_params = ty.param_defs().count();
                let num_expected_params = type_info.params.len();

                // Complain if you try asking for a type and don't provide the expected number
                // of parameters in place of that types generics.
                if num_input_params != num_expected_params {
                    return Err(TypeRegistryTryResolveError::Other(
                        TypeRegistryResolveError::TypeParamsMismatch {
                            type_name: ty.name().to_owned(),
                            expected_params: num_expected_params,
                            provided_params: num_input_params,
                        },
                    ));
                }

                // Build a mapping from generic ident to the concrete type def we've been given.
                // We use this to update generic type names like Vec<T> into concrete ones that the
                // user can access in the registry, like Vec<u32>,
                let param_mapping: SmallVec<[(&str, TypeNameDef<'_>); 4]> = type_info
                    .params
                    .iter()
                    .map(|ident| ident.as_str())
                    .zip(ty.param_defs())
                    .collect();

                // Depending on the type description, we we call the relevant visitor callback
                // with the relevant details.
                match &type_info.desc {
                    TypeShape::StructOf(fields) => {
                        let path_iter = ty_key.name.split("::");
                        let fields_iter = fields.iter().map(|field| Field {
                            name: Some(&field.name),
                            id: apply_param_mapping(pallet, field.value.clone(), &param_mapping),
                        });
                        Ok(visitor.visit_composite(path_iter, fields_iter))
                    }
                    TypeShape::TupleOf(tys) => {
                        let type_ids = tys
                            .iter()
                            .map(|ty| apply_param_mapping(pallet, ty.clone(), &param_mapping));
                        Ok(visitor.visit_tuple(type_ids))
                    }
                    TypeShape::EnumOf(variants) => {
                        let path_iter = ty_key.name.split("::");
                        let variants_iter = variants.iter().map(|var| Variant {
                            index: var.index,
                            name: &var.name,
                            fields: match &var.value {
                                VariantDesc::StructOf(fields) => {
                                    let field_iter = fields.iter().map(|field| Field {
                                        name: Some(&field.name),
                                        id: apply_param_mapping(
                                            pallet,
                                            field.value.clone(),
                                            &param_mapping,
                                        ),
                                    });
                                    Either::A(field_iter)
                                }
                                VariantDesc::TupleOf(fields) => {
                                    let field_iter = fields.iter().map(|ty| Field {
                                        name: None,
                                        id: apply_param_mapping(pallet, ty.clone(), &param_mapping),
                                    });
                                    Either::B(field_iter)
                                }
                            },
                        });
                        Ok(visitor.visit_variant(path_iter, variants_iter))
                    }
                    TypeShape::SequenceOf(seq) => {
                        let path_iter = ty_key.name.split("::");
                        let type_id = apply_param_mapping(pallet, seq.clone(), &param_mapping);
                        Ok(visitor.visit_sequence(path_iter, type_id))
                    }
                    TypeShape::BitSequence { order, store } => {
                        let order = apply_param_mapping(pallet, order.clone(), &param_mapping);
                        let store = apply_param_mapping(pallet, store.clone(), &param_mapping);

                        let order_visitor = order_visitor();
                        let store_visitor = store_visitor();

                        // This is quite verbose because, in the event of an error, we need to
                        // change the visitor type being handed back while avoiding consuming it
                        // in something like a `.map_err()` closure.
                        macro_rules! resolve_format {
                            ($ty:ident, $visitor:ident, $err_variant:ident) => {{
                                match self.try_resolve_type($ty, $visitor) {
                                    Ok(Some(v)) => v,
                                    Ok(None) => {
                                        return Err(TypeRegistryTryResolveError::Other(
                                            TypeRegistryResolveError::$err_variant,
                                        ))
                                    }
                                    Err(TypeRegistryTryResolveError::Other(e)) => {
                                        return Err(TypeRegistryTryResolveError::Other(e))
                                    }
                                    Err(TypeRegistryTryResolveError::TypeNotFound {
                                        name, ..
                                    }) => {
                                        return Err(TypeRegistryTryResolveError::TypeNotFound {
                                            name,
                                            visitor,
                                        })
                                    }
                                }
                            }};
                        }

                        let order_format =
                            resolve_format!(order, order_visitor, UnexpectedBitOrderType);
                        let store_format =
                            resolve_format!(store, store_visitor, UnexpectedBitStoreType);

                        Ok(visitor.visit_bit_sequence(store_format, order_format))
                    }
                    TypeShape::Compact(ty) => {
                        let type_id = apply_param_mapping(pallet, ty.clone(), &param_mapping);
                        Ok(visitor.visit_compact(type_id))
                    }
                    TypeShape::Primitive(p) => Ok(visitor.visit_primitive(*p)),
                    TypeShape::AliasOf(ty) => {
                        let type_id = apply_param_mapping(pallet, ty.clone(), &param_mapping);
                        self.try_resolve_type(type_id, visitor)
                    }
                }
            }
            TypeNameDef::Unnamed(ty) => {
                let type_ids = ty.param_defs().map(|def| def.into_type_name());
                Ok(visitor.visit_tuple(type_ids))
            }
            TypeNameDef::Array(ty) => {
                let len = ty.length();
                let type_id = ty.param_def().into_type_name();
                Ok(visitor.visit_array(type_id, len))
            }
        }
    }

    /// Resolve some type information by providing the string name of the type,
    /// and a `visitor` which will be called in order to describe how to decode it.
    /// This just creates a [`TypeName`] under the hood and uses that to resolve the
    /// type.
    ///
    /// # Example
    ///
    /// ```rust
    /// use scale_info_legacy::{ TypeRegistry, TypeDescription, TypeShape };
    /// use scale_type_resolver::visitor;
    ///
    /// // Provide a dumb visitor (ie set of callbacks) to tell us about the type that
    /// // we query. Here, all we do is return true if the type is a sequence and
    /// // false otherwise.
    /// let my_visitor = visitor::new((), |_, _| false)
    ///     .visit_sequence(|_, _, _| true);
    ///
    /// // Query the string name in our registry, passing our visitor:
    /// let mut registry = TypeRegistry::basic();
    /// let is_sequence = registry.resolve_type_str("Vec<(bool, u32)>", my_visitor).unwrap();
    ///
    /// assert!(is_sequence);
    /// ```
    pub fn resolve_type_str<'this, V: ResolvedTypeVisitor<'this, TypeId = TypeName>>(
        &'this self,
        type_name_str: &str,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryResolveError> {
        let type_id = TypeName::parse(type_name_str)
            .map_err(|e| TypeRegistryResolveError::TypeNameInvalid(type_name_str.to_owned(), e))?;
        self.resolve_type(type_id, visitor)
    }
}

impl TypeResolver for TypeRegistry {
    type TypeId = TypeName;
    type Error = TypeRegistryResolveError;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        self.resolve_type(type_id, visitor)
    }
}

// We store complex owned keys in our hashmap, but want to do lookups using borrowed values.
// That's surprisingly difficult to do! This is one approach; manually hash the borrowed values
// and then lookup corresponding entries by hash, manually comparing keys to find the right one.
// We need to ensure that the way we are hashing things here corresponds to hashing of `TypeKey`,
// so we manually impl `Hash` and use the same function in both places.
fn lookup<'map>(
    pallet: Option<&str>,
    name: &str,
    map: &'map HashMap<TypeKey, TypeInfo>,
) -> Option<(&'map TypeKey, &'map TypeInfo)> {
    // Manually construct the key hash; pallet first and then name due to struct order.
    let hash = {
        use core::hash::{BuildHasher, Hasher};
        let mut state = map.hasher().build_hasher();
        hash_key(pallet, name, &mut state);
        state.finish()
    };

    // Look up the entry by hash, and then compare keys we get back to find the matching key.
    map.raw_entry().from_hash(hash, |k| k.name == name && k.pallet.as_deref() == pallet)
}

// Dev note: this (and the store_visitor below) must be in a separate fn and not in-line so
// that the compiler can generate one exact type for the visitor. If it was written in line,
// you'd hit a recursion limit because each creation of the visitor would have a unique type,
// which is then passed into `.resolve()` requiring unique codegen, recursively.
fn order_visitor<'resolver>() -> impl scale_type_resolver::ResolvedTypeVisitor<
    'resolver,
    TypeId = TypeName,
    Value = Option<BitsOrderFormat>,
> {
    scale_type_resolver::visitor::new((), |_, _| None).visit_composite(|_, path, _| {
        // use the path to determine whether this is the Lsb0 or Msb0
        // ordering type we're looking for, returning None if not.
        if path.next()? != "bitvec" {
            return None;
        }
        if path.next()? != "order" {
            return None;
        }

        let ident = path.next()?;
        if ident == "Lsb0" {
            Some(BitsOrderFormat::Lsb0)
        } else if ident == "Msb0" {
            Some(BitsOrderFormat::Msb0)
        } else {
            None
        }
    })
}

fn store_visitor<'resolver>() -> impl scale_type_resolver::ResolvedTypeVisitor<
    'resolver,
    TypeId = TypeName,
    Value = Option<BitsStoreFormat>,
> {
    scale_type_resolver::visitor::new((), |_, _| None).visit_primitive(|_, p| {
        // use the primitive type to pick the correct bit store format.
        match p {
            Primitive::U8 => Some(BitsStoreFormat::U8),
            Primitive::U16 => Some(BitsStoreFormat::U16),
            Primitive::U32 => Some(BitsStoreFormat::U32),
            Primitive::U64 => Some(BitsStoreFormat::U64),
            _ => None,
        }
    })
}

/// Takes a TypeName and a mapping from generic ident to new defs, and returns a new TypeName where
/// said generic params are replaced with concrete types.
fn apply_param_mapping(
    pallet: Option<&str>,
    ty: TypeName,
    param_mapping: &SmallVec<[(&str, TypeNameDef<'_>); 4]>,
) -> TypeName {
    let new_ty =
        param_mapping.iter().fold(ty, |ty, (ident, def)| ty.with_substitution(ident, *def));

    // Scope lookups of the new type name to whatever pallet the original was defined in
    if let Some(pallet) = pallet {
        new_ty.in_pallet(pallet)
    } else {
        new_ty
    }
}

// A quick enum iterator to be able to handle two branches without boxing, above.
enum Either<A, B> {
    A(A),
    B(B),
}

impl<Item, A: Iterator<Item = Item>, B: Iterator<Item = Item>> Iterator for Either<A, B> {
    type Item = Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Either::A(a) => a.next(),
            Either::B(b) => b.next(),
        }
    }
}
impl<Item, A: ExactSizeIterator<Item = Item>, B: ExactSizeIterator<Item = Item>> ExactSizeIterator
    for Either<A, B>
{
    fn len(&self) -> usize {
        match self {
            Either::A(a) => a.len(),
            Either::B(b) => b.len(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::boxed::Box;
    use alloc::vec::Vec;

    fn to_resolved_info(type_id: TypeName, types: &TypeRegistry) -> ResolvedTypeInfo {
        use scale_type_resolver::visitor;

        // Build a quick visitor which turns resolved type info
        // into a concrete type for us to check.
        let visitor = visitor::new((), |_, _| panic!("all methods implemented"))
            .visit_not_found(|_| ResolvedTypeInfo::NotFound)
            .visit_composite(|_, _, fields| {
                let fs = fields
                    .map(|f| {
                        let inner_ty = to_resolved_info(f.id, types);
                        (f.name.map(|n| n.to_owned()), inner_ty)
                    })
                    .collect();
                ResolvedTypeInfo::CompositeOf(fs)
            })
            .visit_variant(|_, _, variants| {
                let vs = variants
                    .map(|v| {
                        let fs: Vec<_> = v
                            .fields
                            .map(|f| {
                                let inner_ty = to_resolved_info(f.id, types);
                                (f.name.map(|n| n.to_owned()), inner_ty)
                            })
                            .collect();
                        (v.name.to_owned(), fs)
                    })
                    .collect();
                ResolvedTypeInfo::VariantOf(vs)
            })
            .visit_sequence(|_, _, type_id| {
                ResolvedTypeInfo::SequenceOf(Box::new(to_resolved_info(type_id, types)))
            })
            .visit_array(|_, type_id, len| {
                ResolvedTypeInfo::ArrayOf(Box::new(to_resolved_info(type_id, types)), len)
            })
            .visit_tuple(|_, type_ids| {
                let ids = type_ids.map(|id| to_resolved_info(id, types)).collect();
                ResolvedTypeInfo::TupleOf(ids)
            })
            .visit_primitive(|_, primitive| ResolvedTypeInfo::Primitive(primitive))
            .visit_compact(|_, type_id| {
                ResolvedTypeInfo::Compact(Box::new(to_resolved_info(type_id, types)))
            })
            .visit_bit_sequence(|_, store_format, order_format| {
                ResolvedTypeInfo::BitSequence(store_format, order_format)
            });

        match types.resolve_type(type_id, visitor) {
            Err(e) => ResolvedTypeInfo::Err(e),
            Ok(info) => info,
        }
    }

    fn to_resolved_info_str(type_id_str: &str, types: &TypeRegistry) -> ResolvedTypeInfo {
        let type_id = match TypeName::parse(type_id_str) {
            Ok(id) => id,
            Err(e) => {
                return ResolvedTypeInfo::Err(TypeRegistryResolveError::TypeNameInvalid(
                    type_id_str.to_owned(),
                    e,
                ));
            }
        };
        to_resolved_info(type_id, types)
    }

    #[allow(clippy::type_complexity)]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum ResolvedTypeInfo {
        Err(TypeRegistryResolveError),
        NotFound,
        CompositeOf(Vec<(Option<String>, ResolvedTypeInfo)>),
        VariantOf(Vec<(String, Vec<(Option<String>, ResolvedTypeInfo)>)>),
        SequenceOf(Box<ResolvedTypeInfo>),
        ArrayOf(Box<ResolvedTypeInfo>, usize),
        TupleOf(Vec<ResolvedTypeInfo>),
        Primitive(Primitive),
        Compact(Box<ResolvedTypeInfo>),
        BitSequence(BitsStoreFormat, BitsOrderFormat),
    }

    #[test]
    fn resolve_basic_types() {
        let types = TypeRegistry::basic();

        let cases = [
            ("bool", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("char", ResolvedTypeInfo::Primitive(Primitive::Char)),
            ("String", ResolvedTypeInfo::Primitive(Primitive::Str)),
            ("u8", ResolvedTypeInfo::Primitive(Primitive::U8)),
            ("u16", ResolvedTypeInfo::Primitive(Primitive::U16)),
            ("u32", ResolvedTypeInfo::Primitive(Primitive::U32)),
            ("u64", ResolvedTypeInfo::Primitive(Primitive::U64)),
            ("u128", ResolvedTypeInfo::Primitive(Primitive::U128)),
            ("i8", ResolvedTypeInfo::Primitive(Primitive::I8)),
            ("i16", ResolvedTypeInfo::Primitive(Primitive::I16)),
            ("i32", ResolvedTypeInfo::Primitive(Primitive::I32)),
            ("i64", ResolvedTypeInfo::Primitive(Primitive::I64)),
            ("i128", ResolvedTypeInfo::Primitive(Primitive::I128)),
            (
                "Vec<bool>",
                ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::Primitive(
                    Primitive::Bool,
                ))),
            ),
            ("Box<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("Arc<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("Rc<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            (
                "[String; 32]",
                ResolvedTypeInfo::ArrayOf(
                    Box::new(ResolvedTypeInfo::Primitive(Primitive::Str)),
                    32,
                ),
            ),
            (
                "(bool, u32, Vec<String>)",
                ResolvedTypeInfo::TupleOf(vec![
                    ResolvedTypeInfo::Primitive(Primitive::Bool),
                    ResolvedTypeInfo::Primitive(Primitive::U32),
                    ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::Primitive(
                        Primitive::Str,
                    ))),
                ]),
            ),
            (
                "bitvec::vec::BitVec<u8, bitvec::order::Msb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U8, BitsOrderFormat::Msb0),
            ),
            (
                "bitvec::vec::BitVec<u16, bitvec::order::Msb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U16, BitsOrderFormat::Msb0),
            ),
            (
                "bitvec::vec::BitVec<u32, bitvec::order::Msb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U32, BitsOrderFormat::Msb0),
            ),
            (
                "bitvec::vec::BitVec<u64, bitvec::order::Msb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U64, BitsOrderFormat::Msb0),
            ),
            (
                "bitvec::vec::BitVec<u8, bitvec::order::Lsb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U8, BitsOrderFormat::Lsb0),
            ),
            (
                "bitvec::vec::BitVec<u16, bitvec::order::Lsb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U16, BitsOrderFormat::Lsb0),
            ),
            (
                "bitvec::vec::BitVec<u32, bitvec::order::Lsb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U32, BitsOrderFormat::Lsb0),
            ),
            (
                "bitvec::vec::BitVec<u64, bitvec::order::Lsb0>",
                ResolvedTypeInfo::BitSequence(BitsStoreFormat::U64, BitsOrderFormat::Lsb0),
            ),
            (
                "Option<char>",
                ResolvedTypeInfo::VariantOf(vec![
                    ("None".to_owned(), vec![]),
                    ("Some".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Char))]),
                ]),
            ),
            (
                "Result<char, String>",
                ResolvedTypeInfo::VariantOf(vec![
                    ("Ok".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Char))]),
                    ("Err".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Str))]),
                ]),
            ),
        ];

        for (name, expected) in cases.into_iter() {
            assert_eq!(to_resolved_info_str(name, &types), expected);
        }
    }

    #[test]
    fn resolve_aliases() {
        let mut types = TypeRegistry::basic();

        // We test a bunch of things here:
        // - Multiple indirection of aliases,
        // - Aliases with generics,
        // - That bitvec resolving works through aliases.
        types.insert(
            TypeDescription::new(
                "BitVecLsb0Alias1",
                TypeShape::AliasOf(TypeName::parse("bitvec::order::Lsb0").unwrap()),
            )
            .unwrap(),
        );
        types.insert(
            TypeDescription::new(
                "BitVecLsb0Alias2",
                TypeShape::AliasOf(TypeName::parse("BitVecLsb0Alias1").unwrap()),
            )
            .unwrap(),
        );
        types.insert(
            TypeDescription::new(
                "AliasForU16",
                TypeShape::AliasOf(TypeName::parse("u16").unwrap()),
            )
            .unwrap(),
        );
        types.insert(
            TypeDescription::new(
                "AliasForBitVec<S,O>",
                TypeShape::AliasOf(TypeName::parse("bitvec::vec::BitVec<S,O>").unwrap()),
            )
            .unwrap(),
        );

        let resolved =
            to_resolved_info_str("AliasForBitVec<AliasForU16, BitVecLsb0Alias2>", &types);

        assert_eq!(
            resolved,
            ResolvedTypeInfo::BitSequence(BitsStoreFormat::U16, BitsOrderFormat::Lsb0)
        );
    }

    #[test]
    fn resolve_pallet_scoped_types() {
        const PALLET: &str = "balances";
        let mut types = TypeRegistry::empty();

        // Global types
        types.insert(TypeDescription::new("u16", TypeShape::Primitive(Primitive::U16)).unwrap());
        types.insert(
            TypeDescription::new("Primitive", TypeShape::Primitive(Primitive::U16)).unwrap(),
        );

        // Type in balances pallet to override it. (u128, not u16 here)
        types.insert(
            TypeDescription::new("Primitive", TypeShape::Primitive(Primitive::U128))
                .unwrap()
                .in_pallet(PALLET),
        );

        // A couple of composite scoped types:
        types.insert(
            TypeDescription::new("Foo<T>", TypeShape::SequenceOf(TypeName::parse("T").unwrap()))
                .unwrap()
                .in_pallet(PALLET),
        );
        types.insert(
            TypeDescription::new("Bar<T>", TypeShape::SequenceOf(TypeName::parse("T").unwrap()))
                .unwrap()
                .in_pallet(PALLET),
        );

        // Now, try resolving some types in the context of the "balances" pallet to check that we use scoped types appropriately.
        let scoped_tests = [
            // Will still find global types if not overridden:
            ("u16", ResolvedTypeInfo::Primitive(Primitive::U16)),
            // Will use overridden pallet scoped types:
            ("Primitive", ResolvedTypeInfo::Primitive(Primitive::U128)),
            // Pallet scoped-ness is preserved through complex type lookups:
            (
                "Foo<Primitive>",
                ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::Primitive(
                    Primitive::U128,
                ))),
            ),
            (
                "Foo<Bar<Primitive>>",
                ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::SequenceOf(Box::new(
                    ResolvedTypeInfo::Primitive(Primitive::U128),
                )))),
            ),
        ];

        for (input, expected) in scoped_tests {
            let scoped_name = TypeName::parse_unwrap(input).in_pallet("balances");
            let actual = to_resolved_info(scoped_name, &types);
            assert_eq!(expected, actual, "error with type name {input}");
        }
    }
}
