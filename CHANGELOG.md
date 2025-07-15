# Changelog

The format is based on [Keep a Changelog].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/

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