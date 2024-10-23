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

//! This module provides a struct, [`LookupName`]. This struct represents a single concrete type
//! that can be looked up in the [`crate::TypeRegistry`].

use alloc::{
    borrow::{Cow, ToOwned},
    format,
    string::{String, ToString},
};
use smallstr::SmallString;
use smallvec::SmallVec;

// Re-export errors in our public interface:
pub use parser::{ParseError, ParseErrorKind};

/// The name of a type that you'd like to query in the [`crate::TypeRegistry`]. Use
/// [`LookupName::parse()`] to parse a string into a [`LookupName`], which can then be used
/// to look up the associated details in the registry.
///
/// See [`crate::TypeRegistry::resolve_type()`] for a full example.
///
/// # Example
///
/// ```rust
/// use scale_info_legacy::LookupName;
///
/// let sequence = LookupName::parse("Vec<(bool, u32)>").unwrap();
/// let array = LookupName::parse("[u8; 32]").unwrap();
/// let tuple = LookupName::parse("(bool, u32, Vec<String>)").unwrap();
/// ```
#[derive(Clone)]
pub struct LookupName {
    registry: Registry,
    idx: usize,
    // Setting this means that when we try to resolve this type, we'll
    // look at types defined within the given pallet before considering
    // any global types.
    pallet: Option<String>,
}

// We only implement this because `scale_type_resolver::TypeResolver` requires
// type IDs to impl Default.
impl Default for LookupName {
    fn default() -> Self {
        // Various methods expect the registry to have at least one type in it,
        // so we set the type to be the empty unit type.
        let unit_type = LookupNameInner::Unnamed { params: Params::new() };
        Self { registry: Registry::from_iter([unit_type]), idx: 0, pallet: None }
    }
}

#[cfg(test)]
impl PartialEq for LookupName {
    fn eq(&self, other: &Self) -> bool {
        // Bit of a hack, but it does the trick:
        self.to_string() == other.to_string()
    }
}

impl core::fmt::Debug for LookupName {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.def())
    }
}

impl core::fmt::Display for LookupName {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.def())
    }
}

impl core::str::FromStr for LookupName {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl core::convert::TryFrom<&str> for LookupName {
    type Error = ParseError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        Self::parse(s)
    }
}

impl core::convert::TryFrom<String> for LookupName {
    type Error = ParseError;
    fn try_from(s: String) -> Result<Self, Self::Error> {
        Self::parse(&s)
    }
}

impl serde::Serialize for LookupName {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de> serde::Deserialize<'de> for LookupName {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let s = <Cow<'de, str>>::deserialize(deserializer)?;
        LookupName::parse(&s)
            .map_err(|e| D::Error::custom(format!("Could not deserialize into LookupName: {e}")))
    }
}

impl LookupName {
    /// Parse an input string into a [`LookupName`].
    pub fn parse(input: &str) -> Result<LookupName, ParseError> {
        use yap::IntoTokens;
        let mut tokens = input.into_tokens();
        let mut registry = Registry::new();

        parser::parse_type_name(&mut tokens, &mut registry)?;

        Ok(LookupName {
            // Registry must have at least 1 item in, and the last item
            // we added is always the outermost one we want to point to.
            idx: registry.len() - 1,
            registry,
            pallet: None,
        })
    }

    /// This will scope the lookup such that it can make use of types within the given pallet.
    pub fn in_pallet(mut self, pallet_name: impl Into<String>) -> LookupName {
        self.pallet = Some(pallet_name.into());
        self
    }

    /// The pallet that we should perform this type lookup in.
    pub(crate) fn pallet(&self) -> Option<&str> {
        self.pallet.as_deref()
    }

    /// Remove the pallet value from the type name, leaving `None` in its place.
    pub(crate) fn take_pallet(&mut self) -> Option<String> {
        self.pallet.take()
    }

    /// Substitute a named type with another. This is useful if we have a type name
    /// like `Vec<T>` and want to turn it into a concrete type like `Vec<u32>`.
    pub(crate) fn with_substitution(
        mut self,
        ident: &str,
        replacement: LookupNameDef<'_>,
    ) -> LookupName {
        let original_len = self.registry.len();

        // These are all of the indexes we'll want to swap for something else:
        let indexes_to_replace: SmallVec<[_;2]> = self.registry
            .iter()
            .enumerate()
            .filter(|(_, ty)| matches!(ty, LookupNameInner::Named { name, params } if params.is_empty() && name == ident))
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
                LookupNameInner::Named { params, .. } => update_params(params),
                LookupNameInner::Unnamed { params } => update_params(params),
                LookupNameInner::Array { param, .. } => update_param(param),
            }
        }

        // If the Name index itself needs updating, also do this:
        update_param(&mut self.idx);

        self
    }

    /// Fetch the definition of this type.
    pub(crate) fn def(&self) -> LookupNameDef<'_> {
        self.def_at(self.idx)
    }

    /// Insert a foreign [`LookupNameDef`] into this type's registry, returning the index that it was inserted at.
    fn insert_def(&mut self, ty: LookupNameDef<'_>, free_idxs: &[usize]) -> usize {
        let (idx, registry) = match ty {
            LookupNameDef::Named(t) => (t.idx, &t.handle.registry),
            LookupNameDef::Unnamed(t) => (t.idx, &t.handle.registry),
            LookupNameDef::Array(t) => (t.idx, &t.handle.registry),
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
            LookupNameInner::Named { name, params } => {
                let new_params = params
                    .iter()
                    .map(|idx: &usize| {
                        self.insert_entry_from_other_registry(*idx, registry, free_idxs)
                    })
                    .collect();
                LookupNameInner::Named { name: name.clone(), params: new_params }
            }
            LookupNameInner::Unnamed { params } => {
                let new_params = params
                    .iter()
                    .map(|idx: &usize| {
                        self.insert_entry_from_other_registry(*idx, registry, free_idxs)
                    })
                    .collect();
                LookupNameInner::Unnamed { params: new_params }
            }
            LookupNameInner::Array { param, length } => {
                let new_param = self.insert_entry_from_other_registry(*param, registry, free_idxs);
                LookupNameInner::Array { param: new_param, length: *length }
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
    fn def_at(&self, idx: usize) -> LookupNameDef<'_> {
        let entry = self.registry.get(idx).expect("idx should exist in registry");

        match entry {
            LookupNameInner::Named { name, params } => {
                LookupNameDef::Named(NamedTypeDef { idx, name, params, handle: self })
            }
            LookupNameInner::Unnamed { params } => {
                LookupNameDef::Unnamed(UnnamedTypeDef { idx, params, handle: self })
            }
            LookupNameInner::Array { param, length } => LookupNameDef::Array(ArrayTypeDef {
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
pub enum LookupNameDef<'tn> {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named(NamedTypeDef<'tn>),
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed(UnnamedTypeDef<'tn>),
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array(ArrayTypeDef<'tn>),
}

impl<'a> core::fmt::Display for LookupNameDef<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LookupNameDef::Named(named) => {
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
            LookupNameDef::Unnamed(unnamed) => {
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
            LookupNameDef::Array(array) => {
                write!(f, "[{}; {}]", array.param_def(), array.length())?;
            }
        }
        Ok(())
    }
}

impl<'tn> LookupNameDef<'tn> {
    /// Convert this back into a [`LookupName`].
    pub fn into_type_name(self) -> LookupName {
        match self {
            LookupNameDef::Named(v) => v.into_type_name(),
            LookupNameDef::Unnamed(v) => v.into_type_name(),
            LookupNameDef::Array(v) => v.into_type_name(),
        }
    }

    #[cfg(test)]
    fn unwrap_named(self) -> NamedTypeDef<'tn> {
        match self {
            LookupNameDef::Named(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an NamedName"),
        }
    }

    #[cfg(test)]
    fn unwrap_unnamed(self) -> UnnamedTypeDef<'tn> {
        match self {
            LookupNameDef::Unnamed(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an UnnamedName"),
        }
    }

    #[cfg(test)]
    fn unwrap_array(self) -> ArrayTypeDef<'tn> {
        match self {
            LookupNameDef::Array(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an ArrayName"),
        }
    }
}

/// The definition of a named type.
#[derive(Debug, Copy, Clone)]
pub struct NamedTypeDef<'tn> {
    name: &'tn str,
    params: &'tn Params,
    handle: &'tn LookupName,
    idx: usize,
}

impl<'tn> NamedTypeDef<'tn> {
    /// Convert this back into a [`LookupName`].
    pub fn into_type_name(self) -> LookupName {
        LookupName {
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
    pub fn param_defs(&self) -> impl Iterator<Item = LookupNameDef<'tn>> {
        self.params.iter().map(|idx| self.handle.def_at(*idx))
    }
}

/// The definition of an unnamed type.
#[derive(Debug, Copy, Clone)]
pub struct UnnamedTypeDef<'tn> {
    params: &'tn Params,
    handle: &'tn LookupName,
    idx: usize,
}

impl<'tn> UnnamedTypeDef<'tn> {
    /// Convert this back into a [`LookupName`].
    pub fn into_type_name(self) -> LookupName {
        LookupName {
            pallet: self.handle.pallet.to_owned(),
            registry: self.handle.registry.clone(),
            idx: self.idx,
        }
    }

    /// Iterate over the type parameter definitions
    pub fn param_defs(&self) -> impl ExactSizeIterator<Item = LookupNameDef<'tn>> {
        self.params.iter().map(|idx| self.handle.def_at(*idx))
    }
}

/// The definition of an array type.
#[derive(Debug, Copy, Clone)]
pub struct ArrayTypeDef<'tn> {
    param: usize,
    length: usize,
    handle: &'tn LookupName,
    idx: usize,
}

impl<'tn> ArrayTypeDef<'tn> {
    /// Convert this back into a [`LookupName`].
    pub fn into_type_name(self) -> LookupName {
        LookupName {
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
    pub fn param_def(&self) -> LookupNameDef<'tn> {
        self.handle.def_at(self.param)
    }
}

// Internal types used:
type Registry = SmallVec<[LookupNameInner; 2]>;
type Params = SmallVec<[usize; 2]>;
type NameStr = SmallString<[u8; 16]>;

/// The internal representation of some type name.
#[derive(Clone, Debug, PartialEq)]
pub enum LookupNameInner {
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

    /// An error that can be emitted as the result of trying to parse a string into a [`LookupName`].
    #[derive(Debug, Clone, PartialEq, Eq, derive_more::Display)]
    #[display("Error parsing string into type name at character {loc}: {err}")]
    pub struct ParseError {
        /// Index into the string denoting the position of the error.
        pub loc: usize,
        /// More information about the error.
        pub err: ParseErrorKind,
    }

    #[cfg(feature = "std")]
    impl std::error::Error for ParseError {}

    impl ParseError {
        /// Construct a new `ParseError` for tokens at the given location.
        pub fn new_at<E: Into<ParseErrorKind>>(err: E, loc: usize) -> Self {
            Self { loc, err: err.into() }
        }
    }

    /// The kind of error that happened attempting to parse a string into a [`LookupName`].
    #[allow(missing_docs)]
    #[derive(Debug, Clone, PartialEq, Eq, derive_more::Display)]
    pub enum ParseErrorKind {
        #[display("The string did not look like a type name at all.")]
        InvalidName,
        #[display("A closing `)` was missing when attempting to parse a tuple type name.")]
        ClosingParenMissing,
        #[display(
            "A closing `>` was missing when attempting to parse the generics of a named type."
        )]
        ClosingAngleBracketMissing,
        #[display("A closing `]` was missing when attempting to parse an array type.")]
        ClosingSquareBracketMissing,
        #[display("The length of the array is invalid; expecting an unsigned integer.")]
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
            registry.push(LookupNameInner::Named {
                name: NameStr::from_str(&name),
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
            registry.push(LookupNameInner::Named { name: NameStr::from_str(&name), params });
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
            registry.push(LookupNameInner::Unnamed { params });
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
            registry.push(LookupNameInner::Array { param, length });
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
    fn parse_path<'a>(input: &mut StrTokens<'a>) -> Cow<'a, str> {
        let path_str = str_slice_from(input, |toks| {
            toks.sep_by(
                |t| {
                    // Handle paths like the '<Foo as Bar>' in <Foo as Bar>::Name.
                    // We just count <'s and >'s and allow anything inside right now.
                    if t.peek()? == '<' {
                        let mut counter = 0;
                        while let Some(tok) = t.next() {
                            if tok == '<' {
                                counter += 1;
                            } else if tok == '>' {
                                counter -= 1;
                                if counter == 0 {
                                    return Some(());
                                }
                            }
                        }
                    }

                    // First char should exist and be a letter.
                    if !t.peek()?.is_alphabetic() {
                        return None;
                    }
                    // Rest can be letters or numbers.
                    t.skip_while(|c| c.is_alphanumeric());
                    Some(())
                },
                |t| {
                    // Our separator is `::`. Whitespace is allowed.
                    t.surrounded_by(|t| t.tokens("::".chars()), |t| skip_whitespace(t))
                },
            )
            .consume();
        });

        normalize_whitespace(path_str)
    }

    // It's possible that we can see type names like this:
    //
    // <Foo \nas   Bar>::path ::to :: SomeType
    //
    // We want to normalize those typenames to be more like this:
    //
    // <Foo as Bar>::path::to::SomeType
    //
    // This is done in two steps.
    // 1. Turn multiple whitespaces into one space (which mainly resolves
    //    the bit in '<>'s).
    // 2. Remove any whitespace from the part of the path after any '>'.
    //
    // Public only so that it can be tested with our other tests.
    pub fn normalize_whitespace(str: &str) -> Cow<'_, str> {
        // Split <Foo as Bar>::some::Path into '<Foo as Bar>' and '::some::Path'
        let idx = idx_after_closing_angle_bracket(&mut str.chars()).unwrap_or(0);
        let trait_as_part = &str[0..idx];
        let path_part = &str[idx..];

        // Check to see if we need to change anything..

        // - We need to normalize at least 1 whitespace char to ' '.
        let change_in_trait_as_part = trait_as_part.chars().any(|c| c.is_whitespace() && c != ' ');
        // - We need to remove N whitespaces in the <Foo as Bar> part.
        let remove_in_trait_as_part = trait_as_part
            .chars()
            .zip(trait_as_part.chars().skip(1))
            .filter(|(a, b)| a.is_whitespace() && b.is_whitespace())
            .count();
        // - We need to remove N whitespaces in the ::path::to::Foo part.
        let remove_in_path_part = path_part.chars().filter(|c| c.is_whitespace()).count();

        // If no changes to be made then return as is.
        if remove_in_trait_as_part == 0 && remove_in_path_part == 0 && !change_in_trait_as_part {
            return Cow::Borrowed(str);
        }

        let mut new_s =
            String::with_capacity(str.len() - remove_in_path_part - remove_in_trait_as_part);

        // Replace whitespaces in "<Trait as Bar>" section for 1 space.
        let mut prev_is_whitespace = false;
        for c in trait_as_part.chars() {
            if c.is_whitespace() {
                if !prev_is_whitespace {
                    prev_is_whitespace = true;
                    new_s.push(' ');
                }
            } else {
                prev_is_whitespace = false;
                new_s.push(c);
            }
        }

        // Remove whitespaces in "foo::bar::Wibble" section.
        path_part.chars().filter(|c| !c.is_whitespace()).for_each(|c| new_s.push(c));

        Cow::Owned(new_s)
    }

    // given eg <<Foo as bar>::Wibble as Bob>::path::To, find the first index of '::path::To'.
    fn idx_after_closing_angle_bracket(s: &mut impl Iterator<Item = char>) -> Option<usize> {
        let mut idx = 0;
        let mut counter = 0;
        for tok in s {
            idx += 1;
            if tok == '<' {
                counter += 1;
            } else if tok == '>' {
                counter -= 1;
                if counter == 0 {
                    return Some(idx);
                }
            }
        }
        None
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

    fn expect_parse(input: &str) -> LookupName {
        match LookupName::parse(input) {
            Ok(tn) => tn,
            Err(e) => panic!("parsing '{input}' failed: {e}"),
        }
    }

    fn expect_parse_fail(input: &str) {
        match LookupName::parse(input) {
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
        expect_parse("<Wibble as Bar<u32>>::to::Foo"); // paths should work.
        expect_parse("<Wibble as Bar<u32>> ::to::\n Foo"); // paths should work with spaces in
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
            let original_ty = LookupName::parse(original).unwrap();
            let replacement = LookupName::parse(replace_with).unwrap();
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
            let ty_name = LookupName::parse(ty_name_str).unwrap();
            assert_eq!(ty_name.to_string(), ty_name_str);
        }
    }

    #[test]
    fn parsing_trait_as_type_paths_works() {
        let cases = [
            ("<Foo as Bar>::Item<A, B>", "<Foo as Bar>::Item<A, B>", vec!["A", "B"]),
            ("<Foo \tas \n\nBar>::Item", "<Foo as Bar>::Item", vec![]),
            (
                "<<Foo<Thing> \tas \n\nBar<A,B>> as Wibble>::Item",
                "<<Foo<Thing> as Bar<A,B>> as Wibble>::Item",
                vec![],
            ),
        ];

        for (actual, expected, expected_params) in cases {
            let name = LookupName::parse(actual)
                .unwrap_or_else(|_| panic!("should be able to parse '{actual}'"));

            let actual_params: Vec<String> =
                name.def().unwrap_named().param_defs().map(|p| p.to_string()).collect();

            assert_eq!(actual_params, expected_params);
            assert_eq!(name.to_string(), expected);
        }
    }

    #[test]
    fn normalize_whitespace_works() {
        let cases = &[
            // Remove spaces in path bit
            ("T:: Something", Cow::Owned("T::Something".to_string())),
            ("T ::Something", Cow::Owned("T::Something".to_string())),
            // Remove spaces in trait bit
            ("<Foo\n\t as \nBar>", Cow::Owned("<Foo as Bar>".to_string())),
            // Replace but not remove spaces in trait bit
            ("<Foo as\nBar>", Cow::Owned("<Foo as Bar>".to_string())),
            // Some complete examples.
            (
                "<T\t as \n\n\tfoo>:: path\n :: Something",
                Cow::Owned("<T as foo>::path::Something".to_string()),
            ),
            (
                "<<Foo   as\tbar>::Wibble \t \nas\nBob> ::path::\nTo",
                Cow::Owned("<<Foo as bar>::Wibble as Bob>::path::To".to_string()),
            ),
            (
                "<<Foo as bar>::Wibble as Bob>::path::To",
                Cow::Borrowed("<<Foo as bar>::Wibble as Bob>::path::To"),
            ),
        ];

        for (input, output) in cases {
            assert_eq!(&parser::normalize_whitespace(input), output);
        }
    }
}
