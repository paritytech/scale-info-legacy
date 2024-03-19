//! This module provides a way to describe the shape of types; [`TypeDesc`].

pub use scale_type_resolver::{BitsOrderFormat,BitsStoreFormat,Primitive};

pub enum TypeDesc {
    StructOf(Vec<(String, TypeDesc)>),
    VariantOf(Vec<(String, TypeDesc)>),
    Sequenceof(Box<TypeDesc>),
    ArrayOf(Box<TypeDesc>, usize),
    TupleOf(Vec<TypeDesc>),
    BitSequence(BitsOrderFormat,BitsStoreFormat),
    Compact(Box<TypeDesc>),
    Primitive(Primitive),
    AliasOf(String),
    Generic(String),
}