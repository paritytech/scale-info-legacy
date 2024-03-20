//! This module provides a way to describe the shape of types; [`TypeDesc`].

pub use scale_type_resolver::{BitsOrderFormat,BitsStoreFormat,Primitive};

/// This describes the shape of a type, with the aim of providing enough information
/// that we know how to SCALE encode or decode some named type.
pub enum TypeDesc {
    /// A "composite" type in scale-info. This contains a list
    /// of fields and
    StructOf(Vec<Field>),
    /// An enum containing a list of variants.
    EnumOf(Vec<Variant>),
    /// A sequence of some type.
    Sequenceof(Box<TypeDesc>),
    /// A fixed length array of some type.
    ArrayOf(Box<TypeDesc>, usize),
    /// A tuple or "unnamed composite" of some types.
    TupleOf(Vec<TypeDesc>),
    /// A bit sequence.
    BitSequence(BitsOrderFormat,BitsStoreFormat),
    /// A compact encoded type.
    Compact(Box<TypeDesc>),
    /// A primitive type.
    Primitive(Primitive),
    /// An alias to some other type in the registry. The
    /// alias can be something like `Vec<u32>` or `[u8; 16]` or `Bar`.
    AliasOf(String),
    /// A generic type parameter with the given name. This must line
    /// up with the parameters given in a [`crate::type_name::TypeName`]
    /// to be valid, ie a type name of `Vec<u32>` would line up with
    /// `TypeDesc::SequenceOf(TypeDesc::Generic("T"))`.
    Generic(String),
}

/// A struct field.
pub struct Field {
    /// The struct field name.
    pub name: String,
    /// The shape of the field value.
    pub value: TypeDesc
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
    TupleOf(Vec<TypeDesc>),
}