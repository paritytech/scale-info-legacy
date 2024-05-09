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

use crate::{TypeRegistry,TypeName};
use crate::type_registry::{TypeRegistryResolveError};
use scale_type_resolver::TypeResolver;



/// This can be constructed from an iterator of [`crate::TypeRegistry`]s. When resolving types
/// via [`scale_type_resolver::TypeResolver::resolve_type()`], it will treat the provided
/// registries as a stack, looking in the last provided registry first and then working back
/// through them until it can find the type, failing with an error if none of the registries
/// contain an answer.
pub struct TypeRegistrySet {
    registries: Vec<TypeRegistry>
}

impl core::iter::FromIterator<TypeRegistry> for TypeRegistrySet {
    fn from_iter<T: IntoIterator<Item = TypeRegistry>>(iter: T) -> Self {
        TypeRegistrySet { registries: iter.into_iter().collect() }
    }
}

impl TypeResolver for TypeRegistrySet {
    type TypeId = TypeName;
    type Error = TypeRegistryResolveError;

    fn resolve_type<'this, V: scale_type_resolver::ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        for registry in self.registries.iter().rev() {
            match registry.try_resolve_type(type_id, visitor) {
                Ok(val) => return val,
                Err(TypeRegistryTryResolveError::TypeNotFound { visitor, .. }) =>
            }
        }
    }
}