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

use alloc::boxed::Box;
use alloc::vec::Vec;
use scale_type_resolver::{TypeResolver,BitsOrderFormat,BitsStoreFormat,Primitive};
use crate::TypeName;

/// Resolve a type name into a [`ResolvedTypeInfo`] output.
pub fn to_resolved_info<T: TypeResolver<TypeId = TypeName>>(type_id: TypeName, types: &T) -> ResolvedTypeInfo<T::Error> {
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

/// Resolve a string into a [`ResolvedTypeInfo`] output.
pub fn to_resolved_info_str<T: TypeResolver<TypeId = TypeName>>(type_id_str: &str, types: &T) -> ResolvedTypeInfo<T::Error> {
    let type_id = match TypeName::parse(type_id_str) {
        Ok(id) => id,
        Err(_e) => {
            return ResolvedTypeInfo::InvalidTypeName(type_id_str.to_owned());
        }
    };
    to_resolved_info(type_id, types)
}

/// Information about some type we've tried to resolve.
#[allow(clippy::type_complexity)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedTypeInfo<E> {
    Err(E),
    InvalidTypeName(String),
    NotFound,
    CompositeOf(Vec<(Option<String>, ResolvedTypeInfo<E>)>),
    VariantOf(Vec<(String, Vec<(Option<String>, ResolvedTypeInfo<E>)>)>),
    SequenceOf(Box<ResolvedTypeInfo<E>>),
    ArrayOf(Box<ResolvedTypeInfo<E>>, usize),
    TupleOf(Vec<ResolvedTypeInfo<E>>),
    Primitive(Primitive),
    Compact(Box<ResolvedTypeInfo<E>>),
    BitSequence(BitsStoreFormat, BitsOrderFormat),
}