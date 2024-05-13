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

//! This module provides a [`ChainTypeRegistry`], which is constructed by deserializing
//! some data into it. JSON is the expected input format, though in theory others can be
//! used too.

use crate::type_registry_set::TypeRegistrySet;
use crate::type_shape::{Field, TypeShape, Variant, VariantDesc};
use crate::{InsertName, LookupName, TypeRegistry};
use hashbrown::HashMap;
use serde::de::Deserialize;
use serde::de::Error;

/// A registry of types that's been defined for a specific chain.
///
/// Use [`ChainTypeRegistry::for_spec_version()`] to get back something that implements
/// [`scale_type_resolver::TypeResolver`]. Use [`serde`] to deserialize something into this
/// struct (the deserialization logic is tuned to work best with `serde_json`, but any self
/// describing format should work so long as it's the right shape).
#[derive(Debug, serde::Deserialize)]
pub struct ChainTypeRegistry {
    // We always include the built in types at a bare minimum, which we'll put here
    // so that we can lend it out as a `TypeRegistrySet` when needed.
    #[serde(skip, default = "TypeRegistry::basic")]
    basics: TypeRegistry,
    #[serde(deserialize_with = "deserialize_global")]
    global: TypeRegistry,
    #[serde(default, deserialize_with = "deserialize_for_spec", rename = "forSpec")]
    for_spec: Vec<((u64, u64), TypeRegistry)>,
}

impl ChainTypeRegistry {
    /// Hand back a [`TypeRegistrySet`] that is able to resolve types for the given spec version.
    pub fn for_spec_version(&self, spec_version: u64) -> TypeRegistrySet<'_> {
        let basics = std::iter::once(&self.basics);
        let globals = core::iter::once(&self.global);
        let for_spec = self
            .for_spec
            .iter()
            .filter(|((min, max), _)| spec_version >= *min && spec_version <= *max)
            .map(|(_, types)| types);

        let all = basics.chain(globals).chain(for_spec);
        TypeRegistrySet::from_iter(all)
    }

    /// Extend this chain type registry with the one provided. In case of any matches, the provided types
    /// will overwrite the existing ones.
    pub fn extend(&mut self, other: ChainTypeRegistry) {
        self.global.extend(other.global);
        self.for_spec.extend(other.for_spec);
    }
}

// Dev note: Everything below relates to deserializing into the above type. Look at the tests to
// see exactly how each part of the deserializing code works.

fn deserialize_global<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<TypeRegistry, D::Error> {
    let chain_types = DeserializableChainTypes::deserialize(deserializer)?;
    Ok(chain_types.into_type_registry())
}
fn deserialize_for_spec<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<((u64, u64), TypeRegistry)>, D::Error> {
    let for_spec = <Vec<DeserializableChainTypesForSpec>>::deserialize(deserializer)?;
    Ok(for_spec.into_iter().map(|s| (s.range, s.types.into_type_registry())).collect())
}

/// This represents the global and per-pallet types for a chain.
#[derive(serde::Deserialize, Default)]
pub struct DeserializableChainTypes {
    #[serde(default)]
    types: HashMap<InsertName, DeserializableShape>,
    #[serde(default, rename = "palletTypes")]
    pallet_types: HashMap<String, HashMap<InsertName, DeserializableShape>>,
}

impl DeserializableChainTypes {
    /// Convert the types that we've deserialized into a [`TypeRegistry`].
    fn into_type_registry(self) -> TypeRegistry {
        let global_types = self.types.into_iter().map(|(k, v)| (k, v.into()));

        let pallet_types = self.pallet_types.into_iter().flat_map(|(pallet, types)| {
            types.into_iter().map(move |(k, v)| (k.in_pallet(pallet.clone()), v.into()))
        });

        TypeRegistry::from_iter(global_types.chain(pallet_types))
    }
}

/// The global and per-pallet types for a chain used within the given spec versions
#[derive(serde::Deserialize)]
pub struct DeserializableChainTypesForSpec {
    range: (u64, u64),
    #[serde(flatten)]
    types: DeserializableChainTypes,
}

/// The shape of a type.
#[derive(Debug, PartialEq)]
enum DeserializableShape {
    AliasOf(LookupName),
    StructOf(Vec<Field>),
    TupleOf(Vec<LookupName>),
    EnumOf(Vec<Variant>),
}

impl From<DeserializableShape> for TypeShape {
    fn from(value: DeserializableShape) -> Self {
        match value {
            DeserializableShape::AliasOf(a) => TypeShape::AliasOf(a),
            DeserializableShape::StructOf(a) => TypeShape::StructOf(a),
            DeserializableShape::EnumOf(a) => TypeShape::EnumOf(a),
            DeserializableShape::TupleOf(a) => TypeShape::TupleOf(a),
        }
    }
}

impl<'de> serde::Deserialize<'de> for DeserializableShape {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct DeserializableShapeVisitor;
        impl<'de> serde::de::Visitor<'de> for DeserializableShapeVisitor {
            type Value = DeserializableShape;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a string, struct or array")
            }

            // A simple alias type name like 'Vec<T>', '(u64, bool)' or 'Foo'.
            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                let name = LookupName::parse(v)
                    .map_err(|e| E::custom(format!("Could not deserialize into AliasOf: {e}")))?;
                Ok(DeserializableShape::AliasOf(name))
            }

            // Either '{ _enum: ... }' for enum descriptions, or '{ a: ..., b: ... }' for struct descriptions.
            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let Some(name) = map.next_key::<String>()? else {
                    // Empty map; treat it as an empty struct then:
                    return Ok(DeserializableShape::StructOf(Vec::new()));
                };

                // Is the value an enum thing?
                if name == "_enum" {
                    let variants: DeserializableEnum = map.next_value()?;
                    return Ok(DeserializableShape::EnumOf(variants.0));
                }

                // Otherwise, treat as a struct and deserialize each field, remembering
                // to deserialize the value for the key we've already deserialized
                let mut fields = Vec::new();
                fields.push(Field { name, value: map.next_value()? });

                while let Some((name, value)) = map.next_entry()? {
                    fields.push(Field { name, value });
                }

                Ok(DeserializableShape::StructOf(fields))
            }

            // An array like '["Vec<T>", "bool"]'. Ultimately similar to writing '(Vec<T>, bool)'
            // to alias to a tuple.
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut tuple_types = Vec::new();
                while let Some(lookup_name) = seq.next_element()? {
                    tuple_types.push(lookup_name)
                }
                Ok(DeserializableShape::TupleOf(tuple_types))
            }

            // 'null' values are equivalent to '()'.
            fn visit_unit<E>(self) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(DeserializableShape::TupleOf(vec![]))
            }
        }

        deserializer.deserialize_any(DeserializableShapeVisitor)
    }
}

struct DeserializableEnum(Vec<Variant>);

impl<'de> serde::Deserialize<'de> for DeserializableEnum {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct DeserializableEnumVisitor;
        impl<'de> serde::de::Visitor<'de> for DeserializableEnumVisitor {
            type Value = DeserializableEnum;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a struct or array of enum variants")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut variants = Vec::new();
                let mut index = 0;
                while let Some((name, value)) =
                    map.next_entry::<String, DeserializableEnumFields>()?
                {
                    variants.push(Variant { index, name, fields: value.0 });
                    index += 1;
                }
                Ok(DeserializableEnum(variants))
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut variants = Vec::new();
                let mut index = 0;
                while let Some(field) = seq.next_element::<DeserializableEnumSeq>()? {
                    let variant = match field {
                        DeserializableEnumSeq::Name(name) => {
                            Variant { index, name, fields: VariantDesc::TupleOf(vec![]) }
                        }
                        DeserializableEnumSeq::Explicit(variant) => variant,
                    };
                    variants.push(variant);
                    index += 1;
                }
                Ok(DeserializableEnum(variants))
            }
        }

        deserializer.deserialize_any(DeserializableEnumVisitor)
    }
}

struct DeserializableEnumFields(VariantDesc);

impl<'de> serde::Deserialize<'de> for DeserializableEnumFields {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let variant_desc = match DeserializableShape::deserialize(deserializer)? {
            DeserializableShape::AliasOf(lookup_name) => VariantDesc::TupleOf(vec![lookup_name]),
            DeserializableShape::StructOf(fields) => VariantDesc::StructOf(fields),
            DeserializableShape::TupleOf(fields) => VariantDesc::TupleOf(fields),
            DeserializableShape::EnumOf(_) => return Err(D::Error::custom("")),
        };
        Ok(DeserializableEnumFields(variant_desc))
    }
}

enum DeserializableEnumSeq {
    Name(String),
    Explicit(Variant),
}

impl<'de> serde::Deserialize<'de> for DeserializableEnumSeq {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct DeserializableEnumSeqVisitor;
        impl<'de> serde::de::Visitor<'de> for DeserializableEnumSeqVisitor {
            type Value = DeserializableEnumSeq;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a string representing a variant name, or a struct of variant name, index and fields")
            }

            fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(DeserializableEnumSeq::Name(v))
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                self.visit_string(v.to_owned())
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut index: Option<u8> = None;
                let mut name: Option<String> = None;
                let mut fields: Option<DeserializableEnumFields> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        "index" => {
                            index = Some(map.next_value()?);
                        }
                        "name" => {
                            name = Some(map.next_value()?);
                        }
                        "fields" => {
                            fields = Some(map.next_value()?);
                        }
                        other => return Err(A::Error::custom(format!(
                            "field '{other}' not expected. Expecting 'index', 'name' or 'fields'"
                        ))),
                    }
                }

                Ok(DeserializableEnumSeq::Explicit(Variant {
                    index: index.ok_or_else(|| A::Error::custom("field 'index' is missing"))?,
                    name: name.ok_or_else(|| A::Error::custom("field 'name' is missing"))?,
                    fields: fields
                        .unwrap_or(DeserializableEnumFields(VariantDesc::TupleOf(vec![])))
                        .0,
                }))
            }
        }

        deserializer.deserialize_any(DeserializableEnumSeqVisitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_utils::{to_resolved_info, ResolvedTypeInfo};
    use crate::LookupName;
    use scale_type_resolver::Primitive;

    fn ln(s: &str) -> LookupName {
        LookupName::parse(s).unwrap()
    }

    #[test]
    fn deserializable_shape_works() {
        let examples = [
            // Basic alias to some type
            (r#""Vec<T>""#, DeserializableShape::AliasOf(ln("Vec<T>"))),
            // Tuples of types
            (r#"["Vec<T>", "bool"]"#, DeserializableShape::TupleOf(vec![ln("Vec<T>"), ln("bool")])),
            // Structs of types
            (
                r#"{ "a": "Vec<T>", "b": "bool" }"#,
                DeserializableShape::StructOf(vec![
                    Field { name: "a".to_owned(), value: ln("Vec<T>") },
                    Field { name: "b".to_owned(), value: ln("bool") },
                ]),
            ),
            // Enum variants without data
            (
                r#"{ "_enum": ["One", "Two", "Three"] }"#,
                DeserializableShape::EnumOf(vec![
                    Variant {
                        index: 0,
                        name: "One".to_owned(),
                        fields: VariantDesc::TupleOf(vec![]),
                    },
                    Variant {
                        index: 1,
                        name: "Two".to_owned(),
                        fields: VariantDesc::TupleOf(vec![]),
                    },
                    Variant {
                        index: 2,
                        name: "Three".to_owned(),
                        fields: VariantDesc::TupleOf(vec![]),
                    },
                ]),
            ),
            // Enum variants with data
            (
                r#"{ "_enum": {"One": ["Vec<T>", "bool"], "Two": null, "Three": {"a": "Vec<T>", "b": "bool"} } }"#,
                DeserializableShape::EnumOf(vec![
                    Variant {
                        index: 0,
                        name: "One".to_owned(),
                        fields: VariantDesc::TupleOf(vec![ln("Vec<T>"), ln("bool")]),
                    },
                    Variant {
                        index: 1,
                        name: "Two".to_owned(),
                        fields: VariantDesc::TupleOf(vec![]),
                    },
                    Variant {
                        index: 2,
                        name: "Three".to_owned(),
                        fields: VariantDesc::StructOf(vec![
                            Field { name: "a".to_owned(), value: ln("Vec<T>") },
                            Field { name: "b".to_owned(), value: ln("bool") },
                        ]),
                    },
                ]),
            ),
            // Enum variants with explicit name, index and fields
            (
                r#"{ "_enum": [{ "name": "One", "index": 3, "fields": ["Vec<T>", "bool"] }] }"#,
                DeserializableShape::EnumOf(vec![Variant {
                    index: 3,
                    name: "One".to_owned(),
                    fields: VariantDesc::TupleOf(vec![ln("Vec<T>"), ln("bool")]),
                }]),
            ),
        ];

        for (json, expected) in examples {
            let actual: DeserializableShape =
                serde_json::from_str(json).expect(&format!("{json} should parse"));
            assert_eq!(actual, expected);
        }
    }

    // Overall sanity check that we can deserialize and work with the whole thing.
    #[test]
    fn can_deserialize_from_json() {
        let json = serde_json::json!({
            // Types that are present globally, regardless of spec version:
            "global": {
                // Types here exist across all pallets.
                "types": {
                    "Foo": "u8",
                    "Tuple": ["bool", "Vec<String>"],
                    "StructOf<T>": { "a": "bool", "b": "T" },
                    "MyBasicEnum": {
                        "_enum": ["One", "Two", "Three"]
                    },
                    "EnumWithData": {
                        "_enum": {
                            "A": "u64",
                            "B": ["bool", "char"],
                            "C": { "field_a": "String", "field_b": "bool" }
                        }
                    }
                },
                // Any type in palletTypes only exists within a certain pallet.
                "palletTypes": {
                    "balances": {
                        "Balance": "u64"
                    },
                    "assets": {
                        "Fee": "u32",
                        "Type": {
                            "_enum": ["One", "Two", "Three"]
                        }
                    }
                }
            },
            // We can define types that are only relevant in a specific spec range.
            // We can have overlaps here; later definitions trump earlier ones if so.
            "forSpec": [
                {
                    // From 0-1000 (inclusive), we'll use these types.
                    "range": [0, 1000],
                    "types": {
                        "Foo": "u64",
                        "Tuple": ["bool", "Vec<String>"],
                        "StructOf<T>": { "a": "bool", "b": "T" },
                    },
                    "palletTypes": {
                        "balances": {
                            "Balance": "u128"
                        },
                    }
                },
                {
                    // From 1001-2000 (inclusive), we'll use these types.
                    "range": [1001, 2000],
                    "types": {
                        "Foo": "String",
                        "Tuple": ["bool", "Vec<String>"],
                        "StructOf<T>": { "a": "bool", "b": "T" },
                    }
                }
            ]
        });

        let tys: ChainTypeRegistry = serde_json::from_value(json).unwrap();

        let resolver = tys.for_spec_version(12345);
        assert_eq!(to_resolved_info("Foo", &resolver), ResolvedTypeInfo::Primitive(Primitive::U8));
        assert_eq!(
            to_resolved_info(
                LookupName::parse("Balance").unwrap().in_pallet("balances"),
                &resolver
            ),
            ResolvedTypeInfo::Primitive(Primitive::U64)
        );

        let resolver = tys.for_spec_version(500);
        assert_eq!(to_resolved_info("Foo", &resolver), ResolvedTypeInfo::Primitive(Primitive::U64));
        assert_eq!(
            to_resolved_info(
                LookupName::parse("Balance").unwrap().in_pallet("balances"),
                &resolver
            ),
            ResolvedTypeInfo::Primitive(Primitive::U128)
        );

        let resolver = tys.for_spec_version(2000);
        assert_eq!(to_resolved_info("Foo", &resolver), ResolvedTypeInfo::Primitive(Primitive::Str));
    }
}
