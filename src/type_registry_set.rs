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

//! This module provides a [`TypeRegistrySet`], which is constructed from a selection of
//! [`crate::TypeRegistry`]'s, and will resolve types by looking through each one in a known order
//! until a match is found. This allows us to compose different sets of types into a single thing
//! which itself also implements [`scale_type_resolver::TypeResolver`].

use crate::type_registry::{TypeRegistryResolveError, TypeRegistryResolveWithParentError};
use crate::{TypeName, TypeRegistry};
use scale_type_resolver::TypeResolver;

/// This can be constructed from an iterator of [`crate::TypeRegistry`]s. When resolving types
/// via [`scale_type_resolver::TypeResolver::resolve_type()`], it will treat the provided
/// registries as a stack, looking in the last provided registry first and then working back
/// through them until it can find the type, failing with an error if none of the registries
/// contain an answer.
pub struct TypeRegistrySet {
    registries: Vec<TypeRegistry>,
}

impl core::iter::FromIterator<TypeRegistry> for TypeRegistrySet {
    fn from_iter<T: IntoIterator<Item = TypeRegistry>>(iter: T) -> Self {
        TypeRegistrySet { registries: iter.into_iter().collect() }
    }
}

impl TypeResolver for TypeRegistrySet {
    type TypeId = TypeName;
    type Error = TypeRegistryResolveError;

    fn resolve_type<
        'this,
        V: scale_type_resolver::ResolvedTypeVisitor<'this, TypeId = Self::TypeId>,
    >(
        &'this self,
        mut type_id: Self::TypeId,
        mut visitor: V,
    ) -> Result<V::Value, Self::Error> {
        for registry in self.registries.iter().rev() {
            match registry.resolve_type_with_parent(self, type_id, visitor) {
                // Found a value! return it.
                Ok(val) => return Ok(val),
                // Hit some other error; return it.
                Err(TypeRegistryResolveWithParentError::Other(e)) => return Err(e),
                // The type wasn't found; we'll continue to the next registry in the vec.
                Err(TypeRegistryResolveWithParentError::TypeNotFound {
                    type_name: tn,
                    visitor: v,
                }) => {
                    type_id = tn;
                    visitor = v;
                }
            }
        }
        // If we get here, then the type wasn't found in any of our registries, so error.
        Err(TypeRegistryResolveError::TypeNotFound)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_utils::{to_resolved_info, ResolvedTypeInfo};
    use crate::type_shape::Primitive;
    use crate::TypeShape;
    use scale_type_resolver::{BitsOrderFormat, BitsStoreFormat};

    fn tn(name: &str) -> TypeName {
        TypeName::parse(name).unwrap()
    }

    #[test]
    fn picks_last_registry_first() {
        let mut a = TypeRegistry::empty();
        a.insert("u8", TypeShape::Primitive(Primitive::U8)).unwrap();
        a.insert("Val", TypeShape::Primitive(Primitive::I8)).unwrap();

        let mut b = TypeRegistry::empty();
        b.insert("Val", TypeShape::Primitive(Primitive::I16)).unwrap();

        let mut c = TypeRegistry::empty();
        c.insert(tn("Val").in_pallet("balances"), TypeShape::Primitive(Primitive::I32)).unwrap();

        // Resolving will look in c, then b, then a.
        let types = TypeRegistrySet::from_iter([a, b, c]);

        // Sanity check; find val decalred inthe "bottom" registry only.
        assert_eq!(to_resolved_info("u8", &types), ResolvedTypeInfo::Primitive(Primitive::U8));
        // Ignores the pallet val since we aren't in said pallet.
        assert_eq!(to_resolved_info("Val", &types), ResolvedTypeInfo::Primitive(Primitive::I16));
        // Use the pallet specific val if the ID we pass is in that pallet.
        assert_eq!(
            to_resolved_info(tn("Val").in_pallet("balances"), &types),
            ResolvedTypeInfo::Primitive(Primitive::I32)
        );
    }

    #[test]
    fn resolve_bitvec_backwards_across_registries() {
        let mut a = TypeRegistry::empty();
        a.insert(
            "BitVec",
            TypeShape::BitSequence { order: tn("bitvec::order::Lsb0"), store: tn("Store") },
        )
        .unwrap();

        let mut b = TypeRegistry::empty();
        b.insert("bitvec::order::Lsb0", TypeShape::StructOf(vec![])).unwrap();

        let mut c = TypeRegistry::empty();
        c.insert("Store", TypeShape::Primitive(Primitive::U8)).unwrap();

        // Resolving will look in c, then b, then a.
        let types = TypeRegistrySet::from_iter([a, b, c]);

        // Order and store types are both in different registries. Not only different,
        // but ones we've already looked in before we get to the BitVec.
        assert_eq!(
            to_resolved_info("BitVec", &types),
            ResolvedTypeInfo::BitSequence(BitsStoreFormat::U8, BitsOrderFormat::Lsb0)
        );
    }

    #[test]
    fn resolve_alias_backwards_across_registries() {
        let mut a = TypeRegistry::empty();
        a.insert("A", TypeShape::AliasOf(tn("B"))).unwrap();

        let mut b = TypeRegistry::empty();
        b.insert("B", TypeShape::AliasOf(tn("C"))).unwrap();

        let mut c = TypeRegistry::empty();
        c.insert("C", TypeShape::Primitive(Primitive::Bool)).unwrap();

        // Resolving will look in c, then b, then a.
        let types = TypeRegistrySet::from_iter([a, b, c]);

        // We try to resolve the alias A, which is in the last registry to be queried.
        // This will need to backtrack to previous registries in the list to resolve.
        assert_eq!(to_resolved_info("A", &types), ResolvedTypeInfo::Primitive(Primitive::Bool));
    }
}
