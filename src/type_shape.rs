// Copyright (C) 2024 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-encode crate.
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

//! This module provides a [`TypeShape`] enum, which describes the shape of a type, or in other
//! words, how it should be SCALE encoded/decoded.

use crate::type_name::TypeName;
use alloc::string::String;
use alloc::vec::Vec;

pub use scale_type_resolver::{BitsOrderFormat, BitsStoreFormat, Primitive};

/// This describes the shape of a type, with the aim of providing enough information
/// that we know how to SCALE encode or decode some named type.
#[derive(Debug, Clone)]
pub enum TypeShape {
    /// A "named composite" type in scale-info. This contains a list
    /// of fields.
    StructOf(Vec<Field>),
    /// An "unnamed composite" type in scale-info.
    TupleOf(Vec<TypeName>),
    /// An enum containing a list of variants.
    EnumOf(Vec<Variant>),
    /// A sequence of some type.
    SequenceOf(TypeName),
    /// A bit sequence.
    BitSequence {
        /// The order type is expected to resolve to a type with the path
        /// `bitvec::order::Lsb0` or `bitvec::order::Msb0`.
        order: TypeName,
        /// The store type is expected to resolve to a primitive U8/U16/U32/U64.
        store: TypeName,
    },
    /// A compact encoded type.
    Compact(TypeName),
    /// A primitive type.
    Primitive(Primitive),
    /// An alias to some other type in the registry. The
    /// alias can be something like `Vec<T>` or `[u8; 16]` or `Bar`.
    AliasOf(TypeName),
}

/// A struct field.
#[derive(Debug, Clone)]
pub struct Field {
    /// The struct field name.
    pub name: String,
    /// The shape of the field value.
    pub value: TypeName,
}

/// An enum variant.
#[derive(Debug, Clone)]
pub struct Variant {
    /// The variant index.
    pub index: u8,
    /// The variant name.
    pub name: String,
    /// Shape of the variant's arguments.
    pub value: VariantDesc,
}

/// The shape of the variant.
#[derive(Debug, Clone)]
pub enum VariantDesc {
    /// named variant fields are basically a struct.
    StructOf(Vec<Field>),
    /// Unnamed variant fields are basically a tuple of type descriptions.
    TupleOf(Vec<TypeName>),
}
