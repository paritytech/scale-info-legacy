//! This module provides a way to describe the shape of types; [`TypeDesc`].

use crate::ty_name::TyName;

pub use scale_type_resolver::{BitsOrderFormat,BitsStoreFormat,Primitive};

/// This describes the shape of a type, with the aim of providing enough information
/// that we know how to SCALE encode or decode some named type.
pub enum TyDesc {
    /// A "named composite" type in scale-info. This contains a list
    /// of fields.
    StructOf(Vec<Field>),
    /// An "unnamed composite" type in scale-info.
    TupleOf(Vec<TyName>),
    /// An enum containing a list of variants.
    EnumOf(Vec<Variant>),
    /// A sequence of some type.
    Sequenceof(TyName),
    /// A bit sequence.
    BitSequence {
        /// The order type is expected to resolve to a type with the path
        /// `bitvec::order::Lsb0` or `bitvec::order::Msb0`.
        order: TyName,
        /// The store type is expected to resolve to a primitive U8/U16/U32/U64.
        store: TyName
    },
    /// A compact encoded type.
    Compact(TyName),
    /// A primitive type.
    Primitive(Primitive),
    /// An alias to some other type in the registry. The
    /// alias can be something like `Vec<T>` or `[u8; 16]` or `Bar`.
    AliasOf(TyName),
}

/// A struct field.
pub struct Field {
    /// The struct field name.
    pub name: String,
    /// The shape of the field value.
    pub value: TyName
}

/// An enum variant.
pub struct Variant {
    /// The variant index.
    pub index: u8,
    /// The variant name.
    pub name: String,
    /// Shape of the variant's arguments.
    pub value: VariantDesc
}

/// The shape of the variant.
pub enum VariantDesc {
    /// named variant fields are basically a struct.
    StructOf(Vec<Field>),
    /// Unnamed variant fields are basically a tuple of type descriptions.
    TupleOf(Vec<TyName>),
}
