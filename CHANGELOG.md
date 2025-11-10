# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

## 0.3.0 (2025-11-10)

- Improve the `special::Unknown` type to be quicker to construct and to deny _any_ decoding.
- Add a couple of helpers to `LookupName` (`::array()` and `::unnamed()`) to make it easy to construct tuple or array `LookupName`s without any shenanigane involving wrapping strings in tuple/array syntax and re-parsing. 
- Improve Runtime API iteration and add better guarantees around it so that upstream libraries can use it more reliably.

## 0.2.6 (2025-11-05)

- Add a `special::Unknown` type to the default types that are defined by a `TypeRegistry`. Arbitrary bytes are highly likely to fail to decode into `special::Unknown`, and so it can be used to denote types that we know exist (and perhaps need to have defined) but don't know how to actually decode.

## 0.2.5 (2025-11-03)

- Add proper support for `PartialEq`, `Eq`, `PartialOrd`, `Ord` and `Hash` to `LookupName` (and `Ord` + `PartialOrd` to `InsertName`). This most notably allows both of these types to be used as keys in HashMaps / BTreeMaps.

## 0.2.4 (2025-10-08)

- Add support for defining Runtime APIs ([#22](https://github.com/paritytech/scale-info-legacy/pull/22)). This is useful because prior to V15 metadata, we had no Runtime API information, and so we can define such APIs here instead.

## 0.2.3 (2025-07-15)

- Provide a [`ChainTypeRegistry::empty()`] function to allow an empty set of types to be used as a placeholder.

## 0.2.2 (2024-10-23)

- Bump derive_more from 0.99.6 to 1.0.0 ([#13](https://github.com/paritytech/scale-info-legacy/pull/13))
- Bump hashbrown from 0.4 to 0.5 ([#14](https://github.com/paritytech/scale-info-legacy/pull/14))

## 0.2.1 (2024-09-25)

- Normalize type names a little more, making a type like `<Foo \nas   Bar>::path ::to :: SomeType` in the metadata be normalized to `<Foo as Bar>::path::to::SomeType`, so it's easy to define such a type name for lookup.

## 0.2.0 (2024-08-08)

- Allow types to be declared with the same name but different numbers of generic parameters (ie `BalanceOf<T>` and `BalanceOf<T,I>`). See [#9](https://github.com/paritytech/scale-info-legacy/pull/9). This is a breaking change because it removes an error variant related to generic parameter mismatch.

## 0.1.1 (2024-07-26)

- Support parsing trait as type paths like "<Foo as Trait>::Item", and allow prepending to `TypeRegistrySet`s ([#5](https://github.com/paritytech/scale-info-legacy/pull/5)).
- Make InsertName and LookupName Debug the same as Display ([#6](https://github.com/paritytech/scale-info-legacy/pull/6)).

## 0.1.0

Initial release. See the README for more information.

## 0.0.1

Placeholder release