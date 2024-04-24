//! This module provides a [`TypeRegistry`], which can be used to store and resolve
//! type information for types based on their names.

use std::collections::HashMap;
use std::iter::ExactSizeIterator;
use smallvec::SmallVec;
use crate::ty_desc::{ self, Shape, VariantDesc, Primitive };
use crate::ty_name::{ self, Name, NameDef };
use crate::ty::Ty;
use scale_type_resolver::{BitsOrderFormat, BitsStoreFormat, Field, ResolvedTypeVisitor, TypeResolver, Variant};

/// An error resolving types.
#[allow(missing_docs)]
#[derive(Debug,Clone,PartialEq,Eq,derive_more::Display)]
pub enum TypeRegistryResolveError {
    #[display(fmt = "'{_0}' is not a valid type name: {_1}")]
    TypeNameInvalid(String, ty_name::ParseError),
    #[display(fmt = "Type '{_0}' not found")]
    TypeNotFound(String),
    #[display(fmt = "Wrong number of params provided for {type_name}: expected {expected_params} but got {provided_params}")]
    TypeParamsMismatch {
        type_name: String,
        expected_params: usize,
        provided_params: usize,
    },
    #[display(fmt = "Bitvecs must have an order type with the path bitvec::order::Msb0 or bitvec::order::Lsb0")]
    UnexpectedBitOrderType,
    #[display(fmt = "Bitvecs must have a store type which resolves to a primitive u8, u16, u32 or u64 type.")]
    UnexpectedBitStoreType
}

/// The type info stored in the registry against a given named type.
struct TypeInfo {
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    // A description of the shape of the type.
    desc: Shape
}

/// A type registry.
pub struct TypeRegistry {
    // A hash from the name of a type (like `Vec` or `usize`) to a description
    // of the shape of the type (which may involve generic params or just be
    // concrete types or aliases to other types).
    types: HashMap<String, TypeInfo>,
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
            ("bool", Shape::Primitive(Primitive::Bool)),
            ("char", Shape::Primitive(Primitive::Char)),
            ("u8", Shape::Primitive(Primitive::U8)),
            ("u16", Shape::Primitive(Primitive::U16)),
            ("u32", Shape::Primitive(Primitive::U32)),
            ("u64", Shape::Primitive(Primitive::U64)),
            ("u128", Shape::Primitive(Primitive::U128)),
            ("u256", Shape::Primitive(Primitive::U256)),
            ("i8", Shape::Primitive(Primitive::I8)),
            ("i16", Shape::Primitive(Primitive::I16)),
            ("i32", Shape::Primitive(Primitive::I32)),
            ("i64", Shape::Primitive(Primitive::I64)),
            ("i128", Shape::Primitive(Primitive::I128)),
            ("i256", Shape::Primitive(Primitive::I256)),
            ("str", Shape::Primitive(Primitive::Str)),
            ("String", Shape::Primitive(Primitive::Str)),
            ("Box<T>", Shape::AliasOf(Name::parse_unwrap("T"))),
            ("Arc<T>", Shape::AliasOf(Name::parse_unwrap("T"))),
            ("Rc<T>", Shape::AliasOf(Name::parse_unwrap("T"))),
            ("Vec<T>", Shape::Sequenceof(Name::parse_unwrap("T"))),
            ("VecDeque<T>", Shape::Sequenceof(Name::parse_unwrap("T"))),
            ("BTreeMap<K,V>", Shape::Sequenceof(Name::parse_unwrap("(K, V)"))),
            ("BTreeSet<V>", Shape::Sequenceof(Name::parse_unwrap("V"))),
            ("BinaryHeap<V>", Shape::Sequenceof(Name::parse_unwrap("V"))),
            ("Cow<T>", Shape::TupleOf(vec![Name::parse_unwrap("T")])),
            ("Option<T>", Shape::EnumOf(vec![
                ty_desc::Variant {
                    index: 0,
                    name: "None".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![])
                },
                ty_desc::Variant {
                    index: 1,
                    name: "Some".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![Name::parse_unwrap("T")])
                },
            ])),
            ("Result<T,E>", Shape::EnumOf(vec![
                ty_desc::Variant {
                    index: 0,
                    name: "Ok".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![Name::parse_unwrap("T")])
                },
                ty_desc::Variant {
                    index: 1,
                    name: "Err".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![Name::parse_unwrap("E")])
                },
            ])),
            ("PhantomData", Shape::TupleOf(vec![])),
            // These exist just so that resolving bitvecs using these store types will work.
            ("bitvec::order::Lsb0", Shape::StructOf(vec![])),
            ("bitvec::order::Msb0", Shape::StructOf(vec![])),
            // So long as the store type is a suitable primitive and the order type one of the above, this will work out.
            ("bitvec::vec::BitVec<Store, Order>", Shape::BitSequence {
                store: Name::parse_unwrap("Store"),
                order: Name::parse_unwrap("Order"),
            })
        ];

        for (name, desc) in basic_types {
            registry.insert(Ty::new(name, desc).expect("basic type should be valid"));
        }

        registry
    }

    /// Insert a new named type into the registry.
    pub fn insert(&mut self, ty: Ty) {
        let (name, params, desc) = ty.into_parts();
        self.types.insert(name, TypeInfo { desc, params });
    }

    /// Resolve some type information by providing a [`TypeName`], which is the
    /// concrete name of a type we want to know how to decode values for, and a
    /// `visitor` which will be called in order to describe how to decode it.
    ///
    /// This is an alias for [`<TypeRegistry as TypeResolver>::resolve_type()`].
    pub fn resolve<'this, V: ResolvedTypeVisitor<'this, TypeId = Name>>(
        &'this self,
        type_id: Name,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryResolveError> {
        self.resolve_type(type_id, visitor)
    }

    /// Resolve some type information by providing the string name of the type,
    /// and a `visitor` which will be called in order to describe how to decode it.
    pub fn resolve_str<'this, V: ResolvedTypeVisitor<'this, TypeId = Name>>(
        &'this self,
        type_name_str: &str,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryResolveError> {
        let type_id = Name::parse(type_name_str).map_err(|e| {
            TypeRegistryResolveError::TypeNameInvalid(type_name_str.to_owned(), e)
        })?;
        self.resolve_type(type_id, visitor)
    }
}

impl <'a> TypeResolver for TypeRegistry {
    type TypeId = Name;
    type Error = TypeRegistryResolveError;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match type_id.def() {
            NameDef::Named(ty) => {
                let Some(type_info) = self.types.get(ty.name()) else {
                    return Err(TypeRegistryResolveError::TypeNotFound(ty.name().to_owned()))
                };

                let num_input_params = ty.param_defs().count();
                let num_expected_params = type_info.params.len();

                // Complain if you try asking for a type and don't provide the expected number
                // of parameters in place of that types generics.
                if num_input_params != num_expected_params {
                    return Err(TypeRegistryResolveError::TypeParamsMismatch {
                        type_name: ty.name().to_owned(),
                        expected_params: num_expected_params,
                        provided_params: num_input_params,
                    })
                }

                // Build a mapping from generic ident to the concrete type def we've been given.
                // We use this to update generic type names like Vec<T> into concrete ones that the
                // user can access in the registry, like Vec<u32>,
                let param_mapping: SmallVec<[(&str, NameDef<'_>); 4]> = type_info.params
                    .iter()
                    .map(|ident| ident.as_str())
                    .zip(ty.param_defs())
                    .collect();

                // Depending on the type description, we we call the relevant visitor callback
                // with the relevant details.
                match &type_info.desc {
                    Shape::StructOf(fields) => {
                        let path_iter = ty.name().split("::").map(|s| s.as_ref());
                        let fields_iter = fields
                            .iter()
                            .map(|field| Field {
                                name: Some(&field.name),
                                id: apply_param_mapping(field.value.clone(), &param_mapping),
                            });
                        Ok(visitor.visit_composite(path_iter, fields_iter))
                    },
                    Shape::TupleOf(tys) => {
                        let type_ids = tys.iter().map(|ty| apply_param_mapping(ty.clone(), &param_mapping));
                        Ok(visitor.visit_tuple(type_ids))
                    },
                    Shape::EnumOf(variants) => {
                        let path_iter = ty.name().split("::").map(|s| s.as_ref());
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
                        Ok(visitor.visit_variant(path_iter, variants_iter))
                    },
                    Shape::Sequenceof(seq) => {
                        let path_iter = ty.name().split("::").map(|s| s.as_ref());
                        let type_id = apply_param_mapping(seq.clone(), &param_mapping);
                        Ok(visitor.visit_sequence(path_iter, type_id))
                    },
                    Shape::BitSequence { order, store } => {
                        let order = apply_param_mapping(order.clone(), &param_mapping);
                        let store = apply_param_mapping(store.clone(), &param_mapping);

                        let order_visitor = order_visitor();
                        let store_visitor = store_visitor();

                        let order_format = self.resolve(order, order_visitor)?
                            .ok_or(TypeRegistryResolveError::UnexpectedBitOrderType)?;
                        let store_format = self.resolve(store, store_visitor)?
                            .ok_or(TypeRegistryResolveError::UnexpectedBitStoreType)?;

                        Ok(visitor.visit_bit_sequence(store_format, order_format))
                    },
                    Shape::Compact(ty) => {
                        let type_id = apply_param_mapping(ty.clone(), &param_mapping);
                        Ok(visitor.visit_compact(type_id))
                    },
                    Shape::Primitive(p) => {
                        Ok(visitor.visit_primitive(*p))
                    },
                    Shape::AliasOf(ty) => {
                        let type_id = apply_param_mapping(ty.clone(), &param_mapping);
                        self.resolve_type(type_id, visitor)
                    },
                }
            },
            NameDef::Unnamed(ty) => {
                let type_ids = ty.param_defs().map(|def| def.into_type_name());
                Ok(visitor.visit_tuple(type_ids))
            },
            NameDef::Array(ty) => {
                let len = ty.length();
                let type_id = ty.param_def().into_type_name();
                Ok(visitor.visit_array(type_id, len))
            },
        }
    }
}

// Dev note: this (and the store_visitor below) must be in a separate fn and not in-line so
// that the compiler can generate one exact type for the visitor. If it was written in line,
// you'd hit a recursion limit because each creation of the visitor would have a unique type,
// which is then passed into `.resolve()` requiring unique codegen, recursively.
fn order_visitor<'resolver>() -> impl scale_type_resolver::ResolvedTypeVisitor<'resolver, TypeId = Name, Value = Option<BitsOrderFormat>> {
    scale_type_resolver::visitor::new((), |_, _| None)
        .visit_composite(|_, path, _| {
            // use the path to determine whether this is the Lsb0 or Msb0
            // ordering type we're looking for, returning None if not.
            if path.next()? != "bitvec" { return None }
            if path.next()? != "order" { return None }

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

fn store_visitor<'resolver>() -> impl scale_type_resolver::ResolvedTypeVisitor<'resolver, TypeId = Name, Value = Option<BitsStoreFormat>> {
    scale_type_resolver::visitor::new((), |_, _| None)
        .visit_primitive(|_, p| {
            // use the primitive type to pick the correct bit store format.
            match p {
                Primitive::U8 => Some(BitsStoreFormat::U8),
                Primitive::U16 => Some(BitsStoreFormat::U16),
                Primitive::U32 => Some(BitsStoreFormat::U32),
                Primitive::U64 => Some(BitsStoreFormat::U64),
                _ => None
            }
        })
}

/// Takes a TypeName and a mapping from generic ident to new defs, and returns a new TypeName where
/// said generic params are replaced with concrete types.
fn apply_param_mapping(ty: Name, param_mapping: &SmallVec<[(&str, NameDef<'_>); 4]>) -> Name {
    param_mapping.iter().fold(ty, |ty, (ident, def)| ty.with_substitution(ident, *def))
}

// A quick enum iterator to be able to handle two branches without boxing, above.
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

#[cfg(test)]
mod test {
    use super::*;

    fn to_resolved_info(type_id: Name, types: &TypeRegistry) -> ResolvedTypeInfo {
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

        match types.resolve(type_id, visitor) {
            Err(e) => ResolvedTypeInfo::Err(e),
            Ok(info) => info,
        }
    }

    fn to_resolved_info_str(type_id_str: &str, types: &TypeRegistry) -> ResolvedTypeInfo {
        let type_id = match Name::parse(type_id_str) {
            Ok(id) => id,
            Err(e) => {
                return ResolvedTypeInfo::Err(TypeRegistryResolveError::TypeNameInvalid(type_id_str.to_owned(), e));
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
            ("Vec<bool>", ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::Primitive(Primitive::Bool)))),
            ("Box<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("Arc<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("Rc<bool>", ResolvedTypeInfo::Primitive(Primitive::Bool)),
            ("[String; 32]", ResolvedTypeInfo::ArrayOf(Box::new(ResolvedTypeInfo::Primitive(Primitive::Str)), 32)),
            ("(bool, u32, Vec<String>)", ResolvedTypeInfo::TupleOf(vec![
                ResolvedTypeInfo::Primitive(Primitive::Bool),
                ResolvedTypeInfo::Primitive(Primitive::U32),
                ResolvedTypeInfo::SequenceOf(Box::new(ResolvedTypeInfo::Primitive(Primitive::Str))),
            ])),
            ("bitvec::vec::BitVec<u8, bitvec::order::Msb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U8, BitsOrderFormat::Msb0)),
            ("bitvec::vec::BitVec<u16, bitvec::order::Msb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U16, BitsOrderFormat::Msb0)),
            ("bitvec::vec::BitVec<u32, bitvec::order::Msb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U32, BitsOrderFormat::Msb0)),
            ("bitvec::vec::BitVec<u64, bitvec::order::Msb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U64, BitsOrderFormat::Msb0)),
            ("bitvec::vec::BitVec<u8, bitvec::order::Lsb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U8, BitsOrderFormat::Lsb0)),
            ("bitvec::vec::BitVec<u16, bitvec::order::Lsb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U16, BitsOrderFormat::Lsb0)),
            ("bitvec::vec::BitVec<u32, bitvec::order::Lsb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U32, BitsOrderFormat::Lsb0)),
            ("bitvec::vec::BitVec<u64, bitvec::order::Lsb0>", ResolvedTypeInfo::BitSequence(BitsStoreFormat::U64, BitsOrderFormat::Lsb0)),
            ("Option<char>", ResolvedTypeInfo::VariantOf(vec![
                ("None".to_owned(), vec![]),
                ("Some".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Char))]),
            ])),
            ("Result<char, String>", ResolvedTypeInfo::VariantOf(vec![
                ("Ok".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Char))]),
                ("Err".to_owned(), vec![(None, ResolvedTypeInfo::Primitive(Primitive::Str))]),
            ]))
        ];

        for (name, expected) in cases.into_iter() {
            assert_eq!(to_resolved_info_str(name, &types), expected);
        }
    }
}