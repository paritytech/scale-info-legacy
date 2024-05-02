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

//! This module provides a struct, [`TypeName`]. This struct represents a single concrete type
//! that can be looked up in the [`crate::TypeRegistry`].

use alloc::{borrow::ToOwned, string::String};
use smallstr::SmallString;
use smallvec::SmallVec;

// Re-export errors in our public interface:
pub use parser::{ParseError, ParseErrorKind};

/// The name of a type that you'd like to query in the [`crate::TypeRegistry`]. Use
/// [`TypeName::parse()`] to parse a string into a [`TypeName`], which can then be used
/// to look up the associated details in the registry.
///
/// See [`crate::TypeRegistry::resolve_type()`] for a full example.
///
/// # Example
///
/// ```rust
/// use scale_info_legacy::{ TypeName };
///
/// let sequence = TypeName::parse("Vec<(bool, u32)>").unwrap();
/// let array = TypeName::parse("[u8; 32]").unwrap();
/// let tuple = TypeName::parse("(bool, u32, Vec<String>)").unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct TypeName {
    registry: Registry,
    idx: usize,
    // Setting this means that when we try to resolve this type, we'll
    // look at types defined within the given pallet before considering
    // any global types.
    pallet: Option<String>,
}

// We only implement this because `scale_type_resolver::TypeResolver` requires
// type IDs to impl Default.
impl Default for TypeName {
    fn default() -> Self {
        // Various methods expect the registry to have at least one type in it,
        // so we set the type to be the empty unit type.
        let unit_type = TypeNameInner::Unnamed { params: Params::new() };
        Self { registry: Registry::from_iter([unit_type]), idx: 0, pallet: None }
    }
}

impl core::fmt::Display for TypeName {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.def())
    }
}

impl core::str::FromStr for TypeName {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl TypeName {
    /// Parse an input string into a [`TypeName`]. Panics if the input
    /// can not be parsed into a valid [`TypeName`].
    pub fn parse_unwrap(input: &str) -> TypeName {
        Self::parse(input).unwrap()
    }

    /// Parse an input string into a [`TypeName`].
    pub fn parse(input: &str) -> Result<TypeName, ParseError> {
        use yap::IntoTokens;
        let mut tokens = input.into_tokens();
        let mut registry = Registry::new();

        parser::parse_type_name(&mut tokens, &mut registry)?;

        Ok(TypeName {
            // Registry must have at least 1 item in, and the last item
            // we added is always the outermost one we want to point to.
            idx: registry.len() - 1,
            registry,
            pallet: None,
        })
    }

    /// Perform a lookup of this type name in the context of some pallet. This means that
    /// types which are defined to exist only within the given pallet will be considered
    /// before any global types.
    pub fn in_pallet(mut self, pallet_name: impl Into<String>) -> TypeName {
        self.pallet = Some(pallet_name.into());
        self
    }

    /// The pallet that we should perform this type lookup in.
    pub(crate) fn pallet(&self) -> Option<&str> {
        self.pallet.as_deref()
    }

    /// Substitute a named type with another. This is useful if we have a type name
    /// like `Vec<T>` and want to turn it into a concrete type like `Vec<u32>`.
    pub(crate) fn with_substitution(
        mut self,
        ident: &str,
        replacement: TypeNameDef<'_>,
    ) -> TypeName {
        let original_len = self.registry.len();

        // These are all of the indexes we'll want to swap for something else:
        let indexes_to_replace: SmallVec<[_;2]> = self.registry
            .iter()
            .enumerate()
            .filter(|(_, ty)| matches!(ty, TypeNameInner::Named { name, params } if params.is_empty() && name == ident))
            .map(|(idx,_)| idx)
            .collect();

        // Nothing to do; return unchanged:
        if indexes_to_replace.is_empty() {
            return self;
        }

        // Insert the replacement type, returning the index to it:
        let replacement_idx = self.insert_def(replacement, &indexes_to_replace);

        // A couple of helpers to replace any params found in indexes_to_replace with the replacement_idx.
        let update_param = |param: &mut usize| {
            if indexes_to_replace.contains(param) {
                *param = replacement_idx;
            }
        };
        let update_params = |params: &mut Params| {
            for param in params.iter_mut() {
                update_param(param);
            }
        };

        // Update _existing_ types pointing to one of the `indexes_to_replace` to point to this new one.
        for (idx, inner) in self.registry.iter_mut().enumerate() {
            if idx >= original_len {
                // Ignore any new types we added.
                break;
            }
            if indexes_to_replace.contains(&idx) {
                // Ignore any types we may have updated (because we may reuse these indexes).
                continue;
            }

            match inner {
                TypeNameInner::Named { params, .. } => update_params(params),
                TypeNameInner::Unnamed { params } => update_params(params),
                TypeNameInner::Array { param, .. } => update_param(param),
            }
        }

        // If the Name index itself needs updating, also do this:
        update_param(&mut self.idx);

        self
    }

    /// Fetch the definition of this type.
    pub(crate) fn def(&self) -> TypeNameDef<'_> {
        self.def_at(self.idx)
    }

    /// Insert a foreign [`TypeNameDef`] into this type's registry, returning the index that it was inserted at.
    fn insert_def(&mut self, ty: TypeNameDef<'_>, free_idxs: &[usize]) -> usize {
        let (idx, registry) = match ty {
            TypeNameDef::Named(t) => (t.idx, &t.handle.registry),
            TypeNameDef::Unnamed(t) => (t.idx, &t.handle.registry),
            TypeNameDef::Array(t) => (t.idx, &t.handle.registry),
        };

        self.insert_entry_from_other_registry(idx, registry, &mut &*free_idxs)
    }

    /// Take a registry and valid index into it, and copy the relevant entries into our own registry,
    /// returning the index at which the given entry ended up.
    fn insert_entry_from_other_registry(
        &mut self,
        idx: usize,
        registry: &Registry,
        free_idxs: &mut &[usize],
    ) -> usize {
        let idx_to_use = free_idxs.first().map(|idx| {
            *free_idxs = &free_idxs[1..];
            *idx
        });

        let new_inner = match &registry.get(idx).expect("type index used which doesn't exist") {
            TypeNameInner::Named { name, params } => {
                let new_params = params
                    .iter()
                    .map(|idx: &usize| {
                        self.insert_entry_from_other_registry(*idx, registry, free_idxs)
                    })
                    .collect();
                TypeNameInner::Named { name: name.clone(), params: new_params }
            }
            TypeNameInner::Unnamed { params } => {
                let new_params = params
                    .iter()
                    .map(|idx: &usize| {
                        self.insert_entry_from_other_registry(*idx, registry, free_idxs)
                    })
                    .collect();
                TypeNameInner::Unnamed { params: new_params }
            }
            TypeNameInner::Array { param, length } => {
                let new_param = self.insert_entry_from_other_registry(*param, registry, free_idxs);
                TypeNameInner::Array { param: new_param, length: *length }
            }
        };

        // Reuse an existing space if possible, else push a new item to the end:
        if let Some(idx_to_use) = idx_to_use {
            self.registry[idx_to_use] = new_inner;
            idx_to_use
        } else {
            let new_idx = self.registry.len();
            self.registry.push(new_inner);
            new_idx
        }
    }

    // Fetch (and expect to exist) a definition at some index.
    fn def_at(&self, idx: usize) -> TypeNameDef<'_> {
        let entry = self.registry.get(idx).expect("one item expected in Name");

        match entry {
            TypeNameInner::Named { name, params } => {
                TypeNameDef::Named(NamedTypeDef { idx, name, params, handle: self })
            }
            TypeNameInner::Unnamed { params } => {
                TypeNameDef::Unnamed(UnnamedTypeDef { idx, params, handle: self })
            }
            TypeNameInner::Array { param, length } => TypeNameDef::Array(ArrayTypeDef {
                idx,
                param: *param,
                length: *length,
                handle: self,
            }),
        }
    }
}

/// The definition of some type.
#[derive(Debug, Copy, Clone)]
pub enum TypeNameDef<'tn> {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named(NamedTypeDef<'tn>),
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed(UnnamedTypeDef<'tn>),
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array(ArrayTypeDef<'tn>),
}

impl<'a> core::fmt::Display for TypeNameDef<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TypeNameDef::Named(named) => {
                write!(f, "{}", named.name())?;
                if !named.params.is_empty() {
                    write!(f, "<")?;
                    let mut fst = true;
                    for param in named.param_defs() {
                        if !fst {
                            write!(f, ", ")?;
                        }
                        fst = false;
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")?;
                }
            }
            TypeNameDef::Unnamed(unnamed) => {
                write!(f, "(")?;
                if !unnamed.params.is_empty() {
                    let mut fst = true;
                    for param in unnamed.param_defs() {
                        if !fst {
                            write!(f, ", ")?;
                        }
                        fst = false;
                        write!(f, "{}", param)?;
                    }
                }
                write!(f, ")")?;
            }
            TypeNameDef::Array(array) => {
                write!(f, "[{}; {}]", array.param_def(), array.length())?;
            }
        }
        Ok(())
    }
}

impl<'tn> TypeNameDef<'tn> {
    /// Convert this back into a [`TypeName`].
    pub fn into_type_name(self) -> TypeName {
        match self {
            TypeNameDef::Named(v) => v.into_type_name(),
            TypeNameDef::Unnamed(v) => v.into_type_name(),
            TypeNameDef::Array(v) => v.into_type_name(),
        }
    }

    #[cfg(test)]
    fn unwrap_named(self) -> NamedTypeDef<'tn> {
        match self {
            TypeNameDef::Named(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an NamedName"),
        }
    }

    #[cfg(test)]
    fn unwrap_unnamed(self) -> UnnamedTypeDef<'tn> {
        match self {
            TypeNameDef::Unnamed(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an UnnamedName"),
        }
    }

    #[cfg(test)]
    fn unwrap_array(self) -> ArrayTypeDef<'tn> {
        match self {
            TypeNameDef::Array(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an ArrayName"),
        }
    }
}

/// The definition of a named type.
#[derive(Debug, Copy, Clone)]
pub struct NamedTypeDef<'tn> {
    name: &'tn str,
    params: &'tn Params,
    handle: &'tn TypeName,
    idx: usize,
}

impl<'tn> NamedTypeDef<'tn> {
    /// Convert this back into a [`TypeName`].
    pub fn into_type_name(self) -> TypeName {
        TypeName {
            pallet: self.handle.pallet.to_owned(),
            registry: self.handle.registry.clone(),
            idx: self.idx,
        }
    }

    /// The type name.
    pub fn name(&self) -> &'tn str {
        self.name
    }

    /// Iterate over the type parameter definitions.
    pub fn param_defs(&self) -> impl Iterator<Item = TypeNameDef<'tn>> {
        self.params.iter().map(|idx| self.handle.def_at(*idx))
    }
}

/// The definition of an unnamed type.
#[derive(Debug, Copy, Clone)]
pub struct UnnamedTypeDef<'tn> {
    params: &'tn Params,
    handle: &'tn TypeName,
    idx: usize,
}

impl<'tn> UnnamedTypeDef<'tn> {
    /// Convert this back into a [`TypeName`].
    pub fn into_type_name(self) -> TypeName {
        TypeName {
            pallet: self.handle.pallet.to_owned(),
            registry: self.handle.registry.clone(),
            idx: self.idx,
        }
    }

    /// Iterate over the type parameter definitions
    pub fn param_defs(&self) -> impl ExactSizeIterator<Item = TypeNameDef<'tn>> {
        self.params.iter().map(|idx| self.handle.def_at(*idx))
    }
}

/// The definition of an array type.
#[derive(Debug, Copy, Clone)]
pub struct ArrayTypeDef<'tn> {
    param: usize,
    length: usize,
    handle: &'tn TypeName,
    idx: usize,
}

impl<'tn> ArrayTypeDef<'tn> {
    /// Convert this back into a [`TypeName`].
    pub fn into_type_name(self) -> TypeName {
        TypeName {
            pallet: self.handle.pallet.to_owned(),
            registry: self.handle.registry.clone(),
            idx: self.idx,
        }
    }

    /// The array length
    pub fn length(&self) -> usize {
        self.length
    }
    /// The array type parameter.
    pub fn param_def(&self) -> TypeNameDef<'tn> {
        self.handle.def_at(self.param)
    }
}

// Internal types used:
type Registry = SmallVec<[TypeNameInner; 2]>;
type Params = SmallVec<[usize; 2]>;
type NameStr = SmallString<[u8; 16]>;

/// The internal representation of some type name.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeNameInner {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named {
        /// The name of the type (eg Vec, i32, bool).
        name: NameStr,
        /// Each of the generic parameters, if any, associated with the type.
        params: Params,
    },
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed {
        /// Each of the types in the tuple.
        params: Params,
    },
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array {
        /// The type in the array.
        param: usize,
        /// The fixed length of the array.
        length: usize,
    },
}

// Logic for parsing strings into type names.
mod parser {
    use super::*;
    use yap::{types::StrTokens, TokenLocation, Tokens};

    /// An error that can be emitted as the result of trying to parse a string into a [`TypeName`].
    #[derive(Debug, Clone, PartialEq, Eq, derive_more::Display)]
    #[display(fmt = "Error parsing string into type name at character {loc}: {err}")]
    pub struct ParseError {
        /// Index into the string denoting the position of the error.
        pub loc: usize,
        /// More information about the error.
        pub err: ParseErrorKind,
    }

    impl ParseError {
        /// Construct a new `ParseError` for tokens at the given location.
        pub fn new_at<E: Into<ParseErrorKind>>(err: E, loc: usize) -> Self {
            Self { loc, err: err.into() }
        }
    }

    /// The kind of error that happened attempting to parse a string into a [`TypeName`].
    #[allow(missing_docs)]
    #[derive(Debug, Clone, PartialEq, Eq, derive_more::Display)]
    pub enum ParseErrorKind {
        #[display(fmt = "The string did not look like a type name at all.")]
        InvalidName,
        #[display(fmt = "A closing `)` was missing when attempting to parse a tuple type name.")]
        ClosingParenMissing,
        #[display(
            fmt = "A closing `>` was missing when attempting to parse the generics of a named type."
        )]
        ClosingAngleBracketMissing,
        #[display(fmt = "A closing `]` was missing when attempting to parse an array type.")]
        ClosingSquareBracketMissing,
        #[display(fmt = "The length of the array is invalid; expecting an unsigned integer.")]
        InvalidUnsignedInt,
    }

    pub fn parse_type_name(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Result<(), ParseError> {
        let loc = input.location();
        try_parse_type_name(input, registry)
            .unwrap_or_else(|| Err(ParseError::new_at(ParseErrorKind::InvalidName, loc.offset())))
    }

    fn try_parse_type_name(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Option<Result<(), ParseError>> {
        yap::one_of!(input;
            parse_unnamed_into_type_name(input, registry),
            parse_array_into_type_name(input, registry),
            parse_named_into_type_name(input, registry),
        )
    }

    // Parse a named type like Vec<bool>, i32, bool, Foo.
    fn parse_named_into_type_name(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Option<Result<(), ParseError>> {
        let name = parse_path(input);
        if name.is_empty() {
            return None;
        }

        skip_whitespace(input);
        if !input.token('<') {
            // No generics; just add the name to the registry
            registry.push(TypeNameInner::Named {
                name: NameStr::from_str(name),
                params: Params::new(),
            });
            return Some(Ok(()));
        }

        let params = match parse_comma_separated_type_names(input, registry) {
            Ok(params) => params,
            Err(err) => return Some(Err(err)),
        };

        if !input.token('>') {
            let loc = input.location().offset();
            Some(Err(ParseError::new_at(ParseErrorKind::ClosingAngleBracketMissing, loc)))
        } else {
            registry.push(TypeNameInner::Named { name: NameStr::from_str(name), params });
            Some(Ok(()))
        }
    }

    // Parse an unnamed (tuple) type like () or (bool, Foo, Bar<T>).
    fn parse_unnamed_into_type_name(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Option<Result<(), ParseError>> {
        if !input.token('(') {
            return None;
        }

        let params = match parse_comma_separated_type_names(input, registry) {
            Ok(params) => params,
            Err(err) => return Some(Err(err)),
        };

        if !input.token(')') {
            let loc = input.location().offset();
            Some(Err(ParseError::new_at(ParseErrorKind::ClosingParenMissing, loc)))
        } else {
            registry.push(TypeNameInner::Unnamed { params });
            Some(Ok(()))
        }
    }

    // Parse a fixed length array like [Foo; 32].
    fn parse_array_into_type_name(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Option<Result<(), ParseError>> {
        if !input.token('[') {
            return None;
        }

        skip_whitespace(input);
        let param = match parse_type_name(input, registry) {
            Ok(()) => registry.len() - 1,
            Err(e) => return Some(Err(e)),
        };

        skip_whitespace(input);
        input.token(';');
        skip_whitespace(input);

        let loc = input.location().offset();
        let length: usize =
            match input.take_while(|toks| toks.is_numeric()).parse::<usize, String>() {
                Ok(n) => n,
                Err(_) => {
                    return Some(Err(ParseError::new_at(ParseErrorKind::InvalidUnsignedInt, loc)))
                }
            };

        if !input.token(']') {
            let loc = input.location().offset();
            Some(Err(ParseError::new_at(ParseErrorKind::ClosingSquareBracketMissing, loc)))
        } else {
            registry.push(TypeNameInner::Array { param, length });
            Some(Ok(()))
        }
    }

    // Parse a list of type names like Foo,Bar,usize. An empty list is allowed.
    fn parse_comma_separated_type_names(
        input: &mut StrTokens<'_>,
        registry: &mut Registry,
    ) -> Result<Params, ParseError> {
        skip_whitespace(input);

        let mut params_iter = input.sep_by(
            |toks| {
                // Try to parse a type name:
                let res = try_parse_type_name(toks, registry)?;
                // If successful, type name will be last item in registry:
                Some(res.map(|()| registry.len() - 1))
            },
            |toks| toks.surrounded_by(|toks| toks.token(','), |toks| skip_whitespace(toks)),
        );

        let mut params = Params::new();
        for res in params_iter.as_iter() {
            let idx = res?;
            params.push(idx);
        }

        skip_whitespace(input);
        // Allow trailing comma but don't mandate it (ie we don't check the bool).
        input.token(',');
        skip_whitespace(input);

        Ok(params)
    }

    // Parse the name/path of a type like `Foo`` or `a::b::Foo`.
    fn parse_path<'a>(input: &mut StrTokens<'a>) -> &'a str {
        str_slice_from(input, |toks| {
            toks.sep_by(
                |t| {
                    // First char should exist and be a letter.
                    if !t.peek()?.is_alphabetic() {
                        return None;
                    }
                    // Rest can be letters or numbers.
                    t.skip_while(|c| c.is_alphanumeric());
                    Some(())
                },
                |t| {
                    // Our separator is `::`.
                    t.tokens("::".chars())
                },
            )
            .consume();
        })
    }

    // Skip over any whitespace, ignoring it.
    fn skip_whitespace(input: &mut StrTokens<'_>) {
        input.skip_while(|t| t.is_whitespace());
    }

    // Return the string slice that encompasses the provided parsing function given.
    fn str_slice_from<'a, F>(input: &mut StrTokens<'a>, f: F) -> &'a str
    where
        F: FnOnce(&mut StrTokens<'a>),
    {
        let before = input.remaining();
        f(input);
        let leftover = input.remaining().len();

        &before[..before.len() - leftover]
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use alloc::borrow::ToOwned;
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;

    fn expect_parse(input: &str) -> TypeName {
        match TypeName::parse(input) {
            Ok(tn) => tn,
            Err(e) => panic!("parsing '{input}' failed: {e}"),
        }
    }

    fn expect_parse_fail(input: &str) {
        match TypeName::parse(input) {
            Ok(tn) => panic!("parsing '{input}' is expected to have failed, but got {tn:?}"),
            Err(_e) => {}
        }
    }

    #[test]
    fn parse_succeeds() {
        expect_parse("()");
        expect_parse("(Foo)"); // Prob don't need to allow this but hey.
        expect_parse("(Foo,)");
        expect_parse("(Foo, usize,    i32)");
        expect_parse("(a,b,c,)");

        expect_parse("path::to::Foo"); // paths should work.
        expect_parse("Foo");
        expect_parse("Foo<>");
        expect_parse("Foo<A>");
        expect_parse("Foo<A, b,   (), (Wibble)>");

        expect_parse("[usize;32]");
        expect_parse("[a::b::Foo<T,A,B> ;32]");
        expect_parse("[bool;    32]");
    }

    #[test]
    fn parse_fails() {
        // Numbers can't come first in identifiers.
        expect_parse_fail("3thing");
        expect_parse_fail("(bool,3)");

        // Arrays need a number second.
        expect_parse_fail("[usize; Foo]");

        // Brackets must be closed
        expect_parse_fail("(Foo, Bar");
        expect_parse_fail("[Foo; 32");
        expect_parse_fail("Foo<A, B");
    }

    #[test]
    fn with_substitution_works() {
        // Tuple with 4 entries:
        // - The original type name.
        // - The ident we want to replace with something else.
        // - The thing to replace the ident with.
        // - The expected type name after replacement.
        let cases = [
            ("Foo<T>", "T", "(A,B,C)", "Foo<(A, B, C)>"),
            ("T", "T", "Vec<u64>", "Vec<u64>"),
            ("(T, T, u32, T, T)", "T", "[u64; 3]", "([u64; 3], [u64; 3], u32, [u64; 3], [u64; 3])"),
            ("Vec<T>", "T", "U", "Vec<U>"),
            ("Foo<T, (A, [T; 32])>", "T", "U", "Foo<U, (A, [U; 32])>"),
            ("Foo<T, (A, [T; 32])>", "T", "(A,B,C)", "Foo<(A, B, C), (A, [(A, B, C); 32])>"),
            // Don't match types with params; they are not generics so should be left alone:
            ("(T<A>, T)", "T", "U", "(T<A>, U)"),
        ];

        for (original, find, replace_with, expected) in cases {
            let original_ty = TypeName::parse_unwrap(original);
            let replacement = TypeName::parse_unwrap(replace_with);
            let new_ty = original_ty.with_substitution(find, replacement.def());
            assert_eq!(expected, new_ty.to_string());
        }
    }

    #[test]
    fn parses_into_expected_shape() {
        let tn = expect_parse("Foo");
        let def = tn.def().unwrap_named();
        assert!(def.name() == "Foo" && def.param_defs().count() == 0);

        let tn = expect_parse("Foo<A>");
        let def = tn.def().unwrap_named();
        assert!(
            def.name() == "Foo" && def.param_defs().next().unwrap().unwrap_named().name() == "A"
        );

        let tn = expect_parse("()");
        let def = tn.def().unwrap_unnamed();
        assert!(def.param_defs().count() == 0);

        let tn = expect_parse("(bool, u32, Bar<A>)");
        let param_names: Vec<String> = tn
            .def()
            .unwrap_unnamed()
            .param_defs()
            .map(|p| p.unwrap_named().name().to_owned())
            .collect();
        assert_eq!(param_names, vec!["bool", "u32", "Bar"]);

        let tn = expect_parse("[Foo; 16]");
        let def = tn.def().unwrap_array();
        assert!(def.length() == 16 && def.param_def().unwrap_named().name() == "Foo");
    }

    #[test]
    fn parsing_complex_nested_type_works() {
        let tn = expect_parse("Foo<(Option<Wibble<[(u8, Bar);12],Compact<()>>>,bool)>");

        // Foo
        let foo = tn.def().unwrap_named();
        assert_eq!(foo.name(), "Foo");

        // Foo<@...@>
        let foo_params: Vec<_> = foo.param_defs().collect();
        assert_eq!(foo_params.len(), 1);

        // Foo<@(...)@>
        let foo_tuple = foo_params[0].unwrap_unnamed();
        assert_eq!(foo_tuple.param_defs().count(), 2);

        // Foo<(@...@)>
        let foo_tuple_params: Vec<_> = foo_tuple.param_defs().collect();
        assert_eq!(foo_tuple_params.len(), 2);
        assert_eq!(foo_tuple_params[0].unwrap_named().name(), "Option");
        assert_eq!(foo_tuple_params[1].unwrap_named().name(), "bool");

        // Foo<(Option<@...@>)>
        let option_params: Vec<_> = foo_tuple_params[0].unwrap_named().param_defs().collect();
        assert_eq!(option_params.len(), 1);

        // Foo<(Option<@Wibble<..>@>)>
        let wibble = option_params[0].unwrap_named();
        assert_eq!(wibble.name(), "Wibble");

        // Foo<(Option<Wibble<@..@>>)>
        let wibble_params: Vec<_> = wibble.param_defs().collect();
        assert_eq!(wibble_params.len(), 2);

        // Foo<(Option<Wibble<@[(u8, Bar);12)]@>>)>
        let arr = wibble_params[0].unwrap_array();
        assert_eq!(arr.length(), 12);
        assert_eq!(arr.param_def().unwrap_unnamed().param_defs().count(), 2);
    }

    #[test]
    fn displaying_types_works() {
        let ty_name_strs = [
            "u32",
            "Foo",
            "Foo<T>",
            "Foo<A, B, C>",
            "[u8; 32]",
            "[Foo<A>; 32]",
            "()",
            "(A, B, C)",
            "Foo<(A, B, C<D>), [u8; 32], Bar<T>>",
        ];

        for ty_name_str in ty_name_strs {
            let ty_name = TypeName::parse_unwrap(ty_name_str);
            assert_eq!(ty_name.to_string(), ty_name_str);
        }
    }
}
