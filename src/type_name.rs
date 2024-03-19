//! This module provides a [`TypeName`], which can be parsed from a string via [`TypeName::parse`]
//! and represents the name of a type.

use yap::{types::StrTokens, IntoTokens, TokenLocation, Tokens};
use smallvec::SmallVec;
use smallstr::SmallString;

/// Representation of a type name. This can be parsed fro ma string via [`TypeName::parse()`],
/// and then the resulting representation explored with [`TypeName::def()`].
#[derive(Debug,Clone)]
pub struct TypeName {
    registry: Registry
}

// We only implement this because `scale_type_resolver::TypeResolver` requires
// type IDs to impl Default.
impl Default for TypeName {
    fn default() -> Self {
        // Various methods expect the registry to have at least oen type in it,
        // so we set the type to be the empty unit type.
        let unit_type = TypeNameInner::Unnamed { params: Params::new() };
        Self { registry: Registry::from_iter([unit_type]) }
    }
}

impl TypeName {
    /// Parse an input string into a [`TypeName`].
    pub fn parse(input: &str) -> Result<TypeName, ParseError> {
        let mut tokens = input.into_tokens();
        let mut registry = Registry::new();
        parse_type_name(&mut tokens, &mut registry)?;
        Ok(TypeName { registry })
    }

    /// Fetch the definition of this type.
    pub fn def<'tn>(&'tn self) -> TypeNameDef<'tn> {
        self.def_at(self.registry.len() - 1)
    }

    // Fetch (and expect to exist) a definition at some index.
    fn def_at<'tn>(&'tn self, idx: usize) -> TypeNameDef<'tn> {
        let entry = self.registry
            .get(idx)
            .expect("one item expected in TypeName");
        match entry {
            TypeNameInner::Named { name, params } => {
                TypeNameDef::Named(NamedTypeName {
                    name,
                    params,
                    handle: self
                })
            },
            TypeNameInner::Unnamed { params } => {
                TypeNameDef::Unnamed(UnnamedTypeName {
                    params,
                    handle: self
                })
            },
            TypeNameInner::Array { param, length } => {
                TypeNameDef::Array(ArrayTypeName {
                    param: *param,
                    length: *length,
                    handle: self
                })
            },
        }
    }
}

/// The definition of some type.
#[derive(Debug,Copy,Clone)]
pub enum TypeNameDef<'tn> {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named(NamedTypeName<'tn>),
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed(UnnamedTypeName<'tn>),
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array(ArrayTypeName<'tn>),
}

#[cfg(test)]
impl <'tn> TypeNameDef<'tn> {
    pub fn unwrap_named(self) -> NamedTypeName<'tn> {
        match self {
            TypeNameDef::Named(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an NamedTypeName")
        }
    }
    pub fn unwrap_unnamed(self) -> UnnamedTypeName<'tn> {
        match self {
            TypeNameDef::Unnamed(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an UnnamedTypeName")
        }
    }
    pub fn unwrap_array(self) -> ArrayTypeName<'tn> {
        match self {
            TypeNameDef::Array(a) => a,
            _ => panic!("Cannot unwrap '{self:?}' into an ArrayTypeName")
        }
    }
}

/// The definition of a named type.
#[derive(Debug,Copy,Clone)]
pub struct NamedTypeName<'tn> {
    name: &'tn str,
    params: &'tn Params,
    handle: &'tn TypeName
}

impl <'tn> NamedTypeName<'tn> {
    /// The type name.
    pub fn name(&self) -> &str {
        self.name
    }

    /// Iterate over the type parameter definitions.
    pub fn param_defs(&self) -> impl Iterator<Item=TypeNameDef<'tn>> {
        let handle = self.handle;
        self.params.iter().map(|idx| handle.def_at(*idx))
    }
}

/// The definition of an unnamed type.
#[derive(Debug,Copy,Clone)]
pub struct UnnamedTypeName<'tn> {
    params: &'tn Params,
    handle: &'tn TypeName
}

impl <'tn, 'a> UnnamedTypeName<'tn> {
    /// Iterate over the type parameter definitions
    pub fn param_defs(&self) -> impl Iterator<Item=TypeNameDef<'tn>> {
        let handle = self.handle;
        self.params.iter().map(|idx| handle.def_at(*idx))
    }
}


/// The definition of an array type.
#[derive(Debug,Copy,Clone)]
pub struct ArrayTypeName<'tn> {
    param: usize,
    length: usize,
    handle: &'tn TypeName
}

impl <'tn> ArrayTypeName<'tn> {
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
type Registry = SmallVec<[TypeNameInner; 4]>;
type Params = SmallVec<[usize; 4]>;

/// The internal representation of some type name.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeNameInner {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named {
        /// The name of the type (eg Vec, i32, bool).
        name: SmallString<[u8;16]>,
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

/// An error that can be emitted as the result of trying to parse a string into a [`TypeName`].
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

/// The kind of error that happened attempting to parse a string into a [`TypeName`].
#[allow(missing_docs)]
#[derive(Debug, derive_more::Display)]
pub enum ParseErrorKind {
    #[display(fmt = "The string did not look like a type name at all.")]
    InvalidTypeName,
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
        .unwrap_or_else(|| Err(ParseError::new_at(ParseErrorKind::InvalidTypeName, loc.offset())))
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
    if !input.peek()?.is_alphabetic() {
        return None
    }

    let name = str_slice_from(
        input,
        |toks| { toks.skip_while(|c| c.is_alphanumeric()); }
    );

    skip_whitespace(input);
    if !input.token('<') {
        // No generics; just add the name to the registry
        registry.push(TypeNameInner::Named { name: SmallString::from_str(name), params: Params::new() });
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
        registry.push(TypeNameInner::Named { name: SmallString::from_str(name), params });
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
        registry.push(TypeNameInner::Unnamed { params });
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
        registry.push(TypeNameInner::Array { param, length });
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

    fn expect_parse(input: &str) -> TypeName {
        match TypeName::parse(input) {
            Ok(tn) => tn,
            Err(e) => panic!("parsing '{input}' failed: {e}")
        }
    }

    #[test]
    fn parse_succeeds() {
        expect_parse("()");
        expect_parse("(Foo)"); // Prob don't need to allow this but hey.
        expect_parse("(Foo,)");
        expect_parse("(Foo, usize,    i32)");
        expect_parse("(a,b,c,)");

        expect_parse("Foo");
        expect_parse("Foo<>");
        expect_parse("Foo<A>");
        expect_parse("Foo<A, b,   (), (Wibble)>");

        expect_parse("[usize;32]");
        expect_parse("[Foo<T,A,B> ;32]");
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
println!("SIZE {}", std::mem::size_of::<TypeNameInner>());
println!("SIZE {}", std::mem::size_of::<TypeName>());
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