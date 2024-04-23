//! This module provides a [`TyName`], which can be parsed from a string via [`TyName::parse`]
//! and represents the name of a type.

use yap::{types::StrTokens, IntoTokens, TokenLocation, Tokens};
use smallvec::SmallVec;
use smallstr::SmallString;

/// An opaque representation of a type ID. This can be parsed from
/// a string via [`TyName::parse()`],
#[derive(Debug,Clone)]
pub struct TyName {
    registry: Registry,
    idx: usize,
}

// We only implement this because `scale_type_resolver::TypeResolver` requires
// type IDs to impl Default.
impl Default for TyName {
    fn default() -> Self {
        // Various methods expect the registry to have at least one type in it,
        // so we set the type to be the empty unit type.
        let unit_type = TyNameInner::Unnamed { params: Params::new() };
        Self {
            registry: Registry::from_iter([unit_type]),
            idx: 0,
        }
    }
}

impl core::str::FromStr for TyName {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl TyName {
    /// Parse an input string into a [`TyName`]. Panics if the input
    /// can not be parsed into a valid [`TyName`].
    pub fn parse_unwrap(input: &str) -> TyName {
        Self::parse(input).unwrap()
    }

    /// Parse an input string into a [`TyName`].
    pub fn parse(input: &str) -> Result<TyName, ParseError> {
        let mut tokens = input.into_tokens();
        let mut registry = Registry::new();

        parse_type_name(&mut tokens, &mut registry)?;

        Ok(TyName {
            // Registry must have at least 1 item in, and the last item
            // we added is always the outermost one we want to point to.
            idx: registry.len() - 1,
            registry
        })
    }

    /// Substitute a named type with another. This is useful if we have a type name
    /// like `Vec<T>` and want to turn it into a concrete type like `Vec<u32>`.
    pub(crate) fn with_substitution<'other>(mut self, ident: &str, replacement: TyNameDef<'other>) -> TyName {
        // These are all of the indexes we'll want to swap for something else:
        let indexes_to_replace: SmallVec<[_;2]> = self.registry
            .iter()
            .enumerate()
            .filter(|(_, ty)| matches!(ty, TyNameInner::Named { name, params } if params.is_empty() && name == ident))
            .map(|(idx,_)| idx)
            .collect();

        // Nothing to do; return unchanged:
        if indexes_to_replace.is_empty() {
            return self
        }

        // Insert the replacement type, returning the index to it:
        let replacement_idx = self.insert_def(replacement);

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

        // Update any types pointing to one of the `indexes_to_replace` to point to this new one.
        for inner in self.registry.iter_mut() {
            match inner {
                TyNameInner::Named { params, .. } => update_params(params),
                TyNameInner::Unnamed { params } => update_params(params),
                TyNameInner::Array { param, .. } => update_param(param),
            }
        }

        // If the TyName index itself needs updating, also do this:
        update_param(&mut self.idx);

        self
    }

    /// Fetch the definition of this type.
    pub(crate) fn def<'tn>(&'tn self) -> TyNameDef<'tn> {
        self.def_at(self.idx)
    }

    /// Insert a foreign `TyNameDef` into this type's registry, returning the index that it was inserted at.
    fn insert_def(&mut self, ty: TyNameDef<'_>) -> usize {
        let (idx, registry) = match ty {
            TyNameDef::Named(t) => (t.idx, &t.handle.registry),
            TyNameDef::Unnamed(t) => (t.idx, &t.handle.registry),
            TyNameDef::Array(t) => (t.idx, &t.handle.registry),
        };

        self.insert_entry_from_other_registry(idx, registry)
    }

    /// Take a registry and valid index into it, and copy the relevant entries into our own registry,
    /// returning the index at which the given entry ended up.
    fn insert_entry_from_other_registry(&mut self, idx: usize, registry: &Registry) -> usize {
        let new_inner = match &registry.get(idx).expect("type index used which doesn't exist") {
            TyNameInner::Named { name, params } => {
                let new_params = params.iter().map(|idx: &usize| self.insert_entry_from_other_registry(*idx, registry)).collect();
                TyNameInner::Named { name: name.clone(), params: new_params }
            },
            TyNameInner::Unnamed { params } => {
                let new_params = params.iter().map(|idx: &usize| self.insert_entry_from_other_registry(*idx, registry)).collect();
                TyNameInner::Unnamed { params: new_params }
            },
            TyNameInner::Array { param, length } => {
                let new_param = self.insert_entry_from_other_registry(*param, registry);
                TyNameInner::Array { param: new_param, length: *length }
            },
        };

        let new_idx = self.registry.len();
        self.registry.push(new_inner);
        new_idx
    }

    // Fetch (and expect to exist) a definition at some index.
    fn def_at<'tn>(&'tn self, idx: usize) -> TyNameDef<'tn> {
        let entry = self.registry
            .get(idx)
            .expect("one item expected in TyName");

        match entry {
            TyNameInner::Named { name, params } => {
                TyNameDef::Named(NamedTyName {
                    name,
                    params,
                    idx,
                    handle: self
                })
            },
            TyNameInner::Unnamed { params } => {
                TyNameDef::Unnamed(UnnamedTyName {
                    params,
                    idx,
                    handle: self
                })
            },
            TyNameInner::Array { param, length } => {
                TyNameDef::Array(ArrayTyName {
                    param: *param,
                    length: *length,
                    idx,
                    handle: self
                })
            },
        }
    }
}

/// The definition of some type.
#[derive(Debug,Copy,Clone)]
pub enum TyNameDef<'tn> {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named(NamedTyName<'tn>),
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed(UnnamedTyName<'tn>),
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array(ArrayTyName<'tn>),
}

impl <'tn> TyNameDef<'tn> {
    /// Convert this back into a [`TyName`].
    pub fn into_type_name(self) -> TyName {
        match self {
            TyNameDef::Named(v) => v.into_type_name(),
            TyNameDef::Unnamed(v) => v.into_type_name(),
            TyNameDef::Array(v) => v.into_type_name(),
        }
    }

    #[cfg(test)]
    fn unwrap_named(self) -> NamedTyName<'tn> {
        match self {
            TyNameDef::Named(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an NamedTyName")
        }
    }

    #[cfg(test)]
    fn unwrap_unnamed(self) -> UnnamedTyName<'tn> {
        match self {
            TyNameDef::Unnamed(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an UnnamedTyName")
        }
    }

    #[cfg(test)]
    fn unwrap_array(self) -> ArrayTyName<'tn> {
        match self {
            TyNameDef::Array(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an ArrayTyName")
        }
    }
}

/// The definition of a named type.
#[derive(Debug,Copy,Clone)]
pub struct NamedTyName<'tn> {
    name: &'tn str,
    params: &'tn Params,
    handle: &'tn TyName,
    idx: usize,
}

impl <'tn> NamedTyName<'tn> {
    /// Convert this back into a [`TyName`].
    pub fn into_type_name(self) -> TyName {
        TyName {
            registry: self.handle.registry.clone(),
            idx: self.idx
        }
    }

    /// The type name.
    pub fn name(&self) -> &'tn str {
        self.name
    }

    /// Iterate over the type parameter definitions.
    pub fn param_defs(&self) -> impl Iterator<Item=TyNameDef<'tn>> {
        let handle = self.handle;
        self.params.iter().map(|idx| handle.def_at(*idx))
    }
}

/// The definition of an unnamed type.
#[derive(Debug,Copy,Clone)]
pub struct UnnamedTyName<'tn> {
    params: &'tn Params,
    handle: &'tn TyName,
    idx: usize,
}

impl <'tn, 'a> UnnamedTyName<'tn> {
    /// Convert this back into a [`TyName`].
    pub fn into_type_name(self) -> TyName {
        TyName {
            registry: self.handle.registry.clone(),
            idx: self.idx
        }
    }

    /// Iterate over the type parameter definitions
    pub fn param_defs(&self) -> impl ExactSizeIterator<Item=TyNameDef<'tn>> {
        let handle = self.handle;
        self.params.iter().map(|idx| handle.def_at(*idx))
    }
}


/// The definition of an array type.
#[derive(Debug,Copy,Clone)]
pub struct ArrayTyName<'tn> {
    param: usize,
    length: usize,
    handle: &'tn TyName,
    idx: usize,
}

impl <'tn> ArrayTyName<'tn> {
    /// Convert this back into a [`TyName`].
    pub fn into_type_name(self) -> TyName {
        TyName {
            registry: self.handle.registry.clone(),
            idx: self.idx
        }
    }

    /// The array length
    pub fn length(&self) -> usize {
        self.length
    }
    /// The array type parameter.
    pub fn param_def(&self) -> TyNameDef<'tn> {
        self.handle.def_at(self.param)
    }
}


// Internal types used:
type Registry = SmallVec<[TyNameInner; 2]>;
type Params = SmallVec<[usize; 2]>;
type Name = SmallString<[u8; 16]>;

/// The internal representation of some type name.
#[derive(Clone, Debug, PartialEq)]
pub enum TyNameInner {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named {
        /// The name of the type (eg Vec, i32, bool).
        name: Name,
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
        length: usize
    }
}

/// An error that can be emitted as the result of trying to parse a string into a [`TyName`].
#[derive(Debug, derive_more::Display)]
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

/// The kind of error that happened attempting to parse a string into a [`TyName`].
#[allow(missing_docs)]
#[derive(Debug, derive_more::Display)]
pub enum ParseErrorKind {
    #[display(fmt = "The string did not look like a type name at all.")]
    InvalidTyName,
    #[display(fmt = "A closing `)` was missing when attempting to parse a tuple type name.")]
    ClosingParenMissing,
    #[display(fmt = "A closing `>` was missing when attempting to parse the generics of a named type.")]
    ClosingAngleBracketMissing,
    #[display(fmt = "A closing `]` was missing when attempting to parse an array type.")]
    ClosingSquareBracketMissing,
    #[display(fmt = "The length of the array is invalid; expecting an unsigned integer.")]
    InvalidUnsignedInt
}

fn parse_type_name<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Result<(), ParseError> {
    let loc = input.location();
    try_parse_type_name(input, registry)
        .unwrap_or_else(|| Err(ParseError::new_at(ParseErrorKind::InvalidTyName, loc.offset())))
}

fn try_parse_type_name<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Option<Result<(), ParseError>> {
    yap::one_of!(input;
        parse_unnamed_into_type_name(input, registry),
        parse_array_into_type_name(input, registry),
        parse_named_into_type_name(input, registry),
    )
}

// Parse a named type like Vec<bool>, i32, bool, Foo.
fn parse_named_into_type_name<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Option<Result<(), ParseError>> {
    let name = parse_path(input);
    if name.is_empty() {
        return None
    }

    skip_whitespace(input);
    if !input.token('<') {
        // No generics; just add the name to the registry
        registry.push(TyNameInner::Named { name: Name::from_str(name), params: Params::new() });
        return Some(Ok(()))
    }

    let params = match parse_comma_separated_type_names(input, registry) {
        Ok(params) => params,
        Err(err) => return Some(Err(err))
    };

    if !input.token('>') {
        let loc = input.location().offset();
        Some(Err(ParseError::new_at(ParseErrorKind::ClosingAngleBracketMissing, loc)))
    } else {
        registry.push(TyNameInner::Named { name: Name::from_str(name), params });
        Some(Ok(()))
    }
}

// Parse an unnamed (tuple) type like () or (bool, Foo, Bar<T>).
fn parse_unnamed_into_type_name<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Option<Result<(), ParseError>> {
    if !input.token('(') {
        return None
    }

    let params = match parse_comma_separated_type_names(input, registry) {
        Ok(params) => params,
        Err(err) => return Some(Err(err))
    };

    if !input.token(')') {
        let loc = input.location().offset();
        Some(Err(ParseError::new_at(ParseErrorKind::ClosingParenMissing, loc)))
    } else {
        registry.push(TyNameInner::Unnamed { params });
        Some(Ok(()))
    }
}

// Parse a fixed length array like [Foo; 32].
fn parse_array_into_type_name<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Option<Result<(), ParseError>> {
    if !input.token('[') {
        return None
    }

    skip_whitespace(input);
    let param = match parse_type_name(input, registry) {
        Ok(()) => registry.len() - 1,
        Err(e) => return Some(Err(e))
    };

    skip_whitespace(input);
    input.token(';');
    skip_whitespace(input);

    let loc = input.location().offset();
    let length: usize = match input.take_while(|toks| toks.is_numeric()).parse::<usize, String>() {
        Ok(n) => n,
        Err(_) => return Some(Err(ParseError::new_at(ParseErrorKind::InvalidUnsignedInt, loc)))
    };

    if !input.token(']') {
        let loc = input.location().offset();
        Some(Err(ParseError::new_at(ParseErrorKind::ClosingSquareBracketMissing, loc)))
    } else {
        registry.push(TyNameInner::Array { param, length });
        Some(Ok(()))
    }
}

// Parse a list of type names like Foo,Bar,usize. An empty list is allowed.
fn parse_comma_separated_type_names<'a>(input: &mut StrTokens<'a>, registry: &mut Registry) -> Result<Params, ParseError> {
    skip_whitespace(input);

    let mut params_iter = input.sep_by(
        |toks| {
            // Try to parse a type name:
            let res = try_parse_type_name(toks, registry)?;
            // If successful, type name will be last item in registry:
            Some(res.map(|()| registry.len() - 1))
        },
        |toks| {
            toks.surrounded_by(
                |toks| toks.token(','),
                |toks| skip_whitespace(toks)
            )
        }
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
    str_slice_from(
        input,
        |toks| {
            toks.sep_by(
                |t| {
                    // First char should exist and be a letter.
                    if !t.peek()?.is_alphabetic() {
                        return None
                    }
                    // Rest can be letters or numbers.
                    t.skip_while(|c| c.is_alphanumeric());
                    Some(())
                },
                |t| {
                    // Our separator is `::`.
                    t.tokens("::".chars())
                }
            ).consume();
        }
    )
}

// Skip over any whitespace, ignoring it.
fn skip_whitespace<'a>(input: &mut StrTokens<'a>) {
    input.skip_while(|t| t.is_whitespace());
}

// Return the string slice that encompasses the provided parsing function given.
fn str_slice_from<'a, F>(input: &mut StrTokens<'a>, f: F) -> &'a str
where
    F: FnOnce(&mut StrTokens<'a>)
{
    let before = input.remaining();
    f(input);
    let leftover = input.remaining().len();

    &before[..before.len() - leftover]
}

#[cfg(test)]
mod test {
    use super::*;

    fn expect_parse(input: &str) -> TyName {
        match TyName::parse(input) {
            Ok(tn) => tn,
            Err(e) => panic!("parsing '{input}' failed: {e}")
        }
    }

    #[test]
    fn parse_path_works() {
        let paths = [
            "a",
            "a::b::c"
        ];

        for path in paths {
            let mut input = path.into_tokens();
            assert_eq!(parse_path(&mut input), path);
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
    #[should_panic]
    fn parse_fails() {
        // Numbers can't come first in identifiers.
        expect_parse("3thing");
        expect_parse("(bool,3)");

        // Arrays need a number second.
        expect_parse("[usize; Foo]");

        // Brackets must be closed
        expect_parse("(Foo, Bar");
        expect_parse("[Foo; 32");
        expect_parse("Foo<A, B");
    }

    #[test]
    fn parses_into_expected_shape() {
        let tn = expect_parse("Foo");
        let def = tn.def().unwrap_named();
        assert!(def.name() == "Foo" && def.param_defs().count() == 0);

        let tn = expect_parse("Foo<A>");
        let def = tn.def().unwrap_named();
        assert!(def.name() == "Foo" && def.param_defs().next().unwrap().unwrap_named().name() == "A");

        let tn = expect_parse("()");
        let def = tn.def().unwrap_unnamed();
        assert!(def.param_defs().count() == 0);

        let tn = expect_parse("(bool, u32, Bar<A>)");
        let param_names: Vec<String> = tn.def()
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
}