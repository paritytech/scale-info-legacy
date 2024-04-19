//! This module provides a [`TypeRegistry`], which can be used to store and resolve
//! type information for types based on their names.

use std::collections::HashMap;
use std::iter::ExactSizeIterator;
use smallvec::SmallVec;
use crate::ty_desc::{ self, TyDesc, VariantDesc, Primitive };
use crate::ty_name::{ TyName, TyNameDef };
use crate::ty::Ty;
use scale_type_resolver::{TypeResolver,ResolvedTypeVisitor,Field,Variant};

/// An error resolving types.
#[allow(missing_docs)]
#[derive(Debug,derive_more::Display)]
pub enum TypeRegistryResolveError {
    #[display(fmt = "Type '{_0}' not found")]
    TypeNotFound(String),
    #[display(fmt = "Wrong number of params provided for {type_name}: expected {expected_params} but got {provided_params}")]
    TypeParamsMismatch {
        type_name: String,
        expected_params: usize,
        provided_params: usize,
    }
}

/// The type info stored in the registry against a given named type.
struct TypeInfo {
    // The generic param names that may be used in the type description below.
    params: SmallVec<[String; 4]>,
    // A description of the shape of the type.
    desc: TyDesc
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

    /// Create a new [`TypeRegistry`] that's prepopulated with built-in rust types.
    pub fn basic() -> Self {
        let mut registry = TypeRegistry::empty();

        let basic_types = [
            ("bool", TyDesc::Primitive(Primitive::Bool)),
            ("char", TyDesc::Primitive(Primitive::Char)),
            ("u8", TyDesc::Primitive(Primitive::U8)),
            ("u16", TyDesc::Primitive(Primitive::U16)),
            ("u32", TyDesc::Primitive(Primitive::U32)),
            ("u64", TyDesc::Primitive(Primitive::U64)),
            ("u128", TyDesc::Primitive(Primitive::U128)),
            ("u256", TyDesc::Primitive(Primitive::U256)),
            ("i8", TyDesc::Primitive(Primitive::I8)),
            ("i16", TyDesc::Primitive(Primitive::I16)),
            ("i32", TyDesc::Primitive(Primitive::I32)),
            ("i64", TyDesc::Primitive(Primitive::I64)),
            ("i128", TyDesc::Primitive(Primitive::I128)),
            ("i256", TyDesc::Primitive(Primitive::I256)),
            ("str", TyDesc::Primitive(Primitive::Str)),
            ("String", TyDesc::Primitive(Primitive::Str)),
            ("Box<T>", TyDesc::AliasOf(TyName::parse_unwrap("T"))),
            ("Arc<T>", TyDesc::AliasOf(TyName::parse_unwrap("T"))),
            ("Rc<T>", TyDesc::AliasOf(TyName::parse_unwrap("T"))),
            ("Vec<T>", TyDesc::Sequenceof(TyName::parse_unwrap("T"))),
            ("VecDeque<T>", TyDesc::Sequenceof(TyName::parse_unwrap("T"))),
            ("BTreeMap<K,V>", TyDesc::Sequenceof(TyName::parse_unwrap("(K, V)"))),
            ("BTreeSet<V>", TyDesc::Sequenceof(TyName::parse_unwrap("V"))),
            ("BinaryHeap<V>", TyDesc::Sequenceof(TyName::parse_unwrap("V"))),
            ("Cow<T>", TyDesc::TupleOf(vec![TyName::parse_unwrap("T")])),
            ("Option<T>", TyDesc::EnumOf(vec![
                ty_desc::Variant {
                    index: 0,
                    name: "None".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![])
                },
                ty_desc::Variant {
                    index: 1,
                    name: "Some".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![TyName::parse_unwrap("T")])
                },
            ])),
            ("Result<T,E>", TyDesc::EnumOf(vec![
                ty_desc::Variant {
                    index: 0,
                    name: "Ok".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![TyName::parse_unwrap("T")])
                },
                ty_desc::Variant {
                    index: 1,
                    name: "Err".to_owned(),
                    value: ty_desc::VariantDesc::TupleOf(vec![TyName::parse_unwrap("E")])
                },
            ])),
            ("PhantomData", TyDesc::TupleOf(vec![])),
            // TODOs:
            // - How to resolve a BitVec? If one provides "BitVec<Lsb0,u8>" for instance. Maybe
            //   need to have a special TyDesc::BitOrderFormat and then use Primitive::U8 etc to work out store format?
            //   so then BitVec<S,O> => TyDesc::BitsequenceOf { store: TyName::parse("S"), order: TyName::parse("O") }.
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
    pub fn resolve<'this, V: ResolvedTypeVisitor<'this, TypeId = TyName>>(
        &'this self,
        type_id: TyName,
        visitor: V,
    ) -> Result<V::Value, TypeRegistryResolveError> {
        self.resolve_type(type_id, visitor)
    }
}

impl <'a> TypeResolver for TypeRegistry {
    type TypeId = TyName;
    type Error = TypeRegistryResolveError;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        match type_id.def() {
            TyNameDef::Named(ty) => {
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
                let param_mapping: SmallVec<[(&str, TyNameDef<'_>); 4]> = type_info.params
                    .iter()
                    .map(|ident| ident.as_str())
                    .zip(ty.param_defs())
                    .collect();

                // Visit the provided visitor with the relevant details.
                match &type_info.desc {
                    TyDesc::StructOf(fields) => {
                        let fields_iter = fields
                            .iter()
                            .map(|field| Field {
                                name: Some(&field.name),
                                id: apply_param_mapping(field.value.clone(), &param_mapping),
                            });
                        Ok(visitor.visit_composite(fields_iter))
                    },
                    TyDesc::TupleOf(tys) => {
                        let type_ids = tys.iter().map(|ty| apply_param_mapping(ty.clone(), &param_mapping));
                        Ok(visitor.visit_tuple(type_ids))
                    },
                    TyDesc::EnumOf(variants) => {
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
                        Ok(visitor.visit_variant(variants_iter))
                    },
                    TyDesc::Sequenceof(ty) => {
                        let type_id = apply_param_mapping(ty.clone(), &param_mapping);
                        Ok(visitor.visit_sequence(type_id))
                    },
                    TyDesc::BitSequence(order, store) => {
                        Ok(visitor.visit_bit_sequence(*store, *order))
                    },
                    TyDesc::Compact(ty) => {
                        let type_id = apply_param_mapping(ty.clone(), &param_mapping);
                        Ok(visitor.visit_compact(type_id))
                    },
                    TyDesc::Primitive(p) => {
                        Ok(visitor.visit_primitive(*p))
                    },
                    TyDesc::AliasOf(ty) => {
                        let type_id = apply_param_mapping(ty.clone(), &param_mapping);
                        self.resolve_type(type_id, visitor)
                    },
                }
            },
            TyNameDef::Unnamed(ty) => {
                let type_ids = ty.param_defs().map(|def| def.into_type_name());
                Ok(visitor.visit_tuple(type_ids))
            },
            TyNameDef::Array(ty) => {
                let len = ty.length();
                let type_id = ty.into_type_name();
                Ok(visitor.visit_array(type_id, len))
            },
        }
    }
}

/// Takes a TypeName and a mapping from generic ident to new defs, and returns a new TypeName where
/// said generic params are replaced with concrete types.
fn apply_param_mapping(ty: TyName, param_mapping: &SmallVec<[(&str, TyNameDef<'_>); 4]>) -> TyName {
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