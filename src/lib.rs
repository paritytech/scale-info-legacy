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

//! This crate provides a [`TypeRegistry`] that is capable of storing and providing back information about
//! historic Substrate based types (ie those that are handed back in pre-V14 metadata). It's somewhat
//! analogous to the [`scale-info`](https://github.com/paritytech/scale-info) crate, but for legacy type
//! information rather than modern type information.
//!
//! See [`TypeRegistry::insert()`] to learn how to add types to the registry, and [`TypeRegistry::resolve_type()`]
//! to learn how to then resolve type information using the registry.
//!
//! This crate, like `scale-info`, can be used in conjunction with crates like:
//! - [`scale-decode`](https://github.com/paritytech/scale-decode) to decode SCALE encoded bytes
//!   into custom types based on this type information.
//! - [`scale-encode`](https://github.com/paritytech/scale-encode) to SCALE encode custom types
//!   into bytes based on this type information.
//! - [`scale-value`](https://github.com/paritytech/scale-value) to SCALE encode or decode from a
//!   `Value` type (a bit like `serde_json`'s `Value` type).

#![cfg_attr(not(feature = "std"), no_std)]
#![deny(missing_docs)]

extern crate alloc;

pub mod type_name;
pub mod type_registry;
pub mod type_registry_set;
pub mod type_shape;

// Export the main types here for ease of use:
pub use {type_name::TypeName, type_registry::TypeRegistry, type_shape::TypeShape};
