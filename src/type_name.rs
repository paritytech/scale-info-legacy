//! This module provides a [`TypeName`], which can be parsed from a string via [`TypeName::parse`]
//! and represents the name of a type.

use yap::{types::StrTokens, IntoTokens, TokenLocation, Tokens};

/// A representation of some type name.
#[derive(Clone, Debug, PartialEq)]
pub enum TypeName<'a> {
    /// Types like `Vec<T>`, `Foo` and `path::to::Bar<A,B>`, `i32`, `bool`
    /// etc are _named_ types.
    Named {
        /// The name of the type (eg Vec, i32, bool).
        name: &'a str,
        /// Each of the generic parameters, if any, associated with the type.
        params: Vec<TypeName<'a>>
    },
    /// Tuples like `()` and `(Foo, Bar<A>)` are _unnamed_ types.
    Unnamed {
        /// Each of the types in the tuple.
        params: Vec<TypeName<'a>>
    },
    /// Fixed length arrays like `[Bar; 32]` are _array_ types.
    Array {
        /// The type in the array.
        param: Box<TypeName<'a>>,
        /// The fixed length of the array.
        length: usize
    }
}

impl <'a> TypeName<'a> {
    /// Parse an input string into a [`TypeName`].
    pub fn parse(input: &'a str) -> Result<TypeName<'_>, ParseError> {
        let mut tokens = input.into_tokens();
        parse_type_name(&mut tokens)
    }

    /// Create a named [`TypeName`] with no parameters.
    pub fn named(name: &'a str) -> TypeName<'a> {
        TypeName::Named { name, params: Vec::new() }
    }

    /// Create a named [`TypeName`] with one parameter.
    pub fn named_with_param(name: &'a str, param: TypeName<'a>) -> TypeName<'a> {
        TypeName::Named { name, params: vec![param] }
    }

    /// Create a named [`TypeName`] with no parameters.
    pub fn named_with_params(name: &'a str, params: Vec<TypeName<'a>>) -> TypeName<'a> {
        TypeName::Named { name, params }
    }

    /// Create an unnamed/tuple [`TypeName`].
    pub fn unnamed(params: Vec<TypeName<'a>>) -> TypeName<'a> {
        TypeName::Unnamed { params }
    }

    /// Create an unnamed/tuple [`TypeName`].
    pub fn array(param: impl Into<Box<TypeName<'a>>>, length: usize) -> TypeName<'a> {
        TypeName::Array { param: param.into(), length }
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

fn parse_type_name<'a>(input: &mut StrTokens<'a>) -> Result<TypeName<'a>, ParseError> {
    let loc = input.location();
    try_parse_type_name(input)
        .unwrap_or_else(|| Err(ParseError::new_at(ParseErrorKind::InvalidTypeName, loc.offset())))
}

fn try_parse_type_name<'a>(input: &mut StrTokens<'a>) -> Option<Result<TypeName<'a>, ParseError>> {
    yap::one_of!(input;
        parse_unnamed_into_type_name(input),
        parse_array_into_type_name(input),
        parse_named_into_type_name(input),
    )
}

// Parse a named type like Vec<bool>, i32, bool, Foo.
fn parse_named_into_type_name<'a>(input: &mut StrTokens<'a>) -> Option<Result<TypeName<'a>, ParseError>> {
    if !input.peek()?.is_alphabetic() {
        return None
    }

    let name = str_slice_from(
        input,
        |toks| { toks.skip_while(|c| c.is_alphanumeric()); }
    );

    skip_whitespace(input);
    if !input.token('<') {
        // No generics; return just the name:
        return Some(Ok(TypeName::Named { name, params: Vec::new() }))
    }

    let params = match parse_comma_separated_type_names(input) {
        Ok(params) => params,
        Err(err) => return Some(Err(err))
    };

    if !input.token('>') {
        let loc = input.location().offset();
        Some(Err(ParseError::new_at(ParseErrorKind::ClosingAngleBracketMissing, loc)))
    } else {
        Some(Ok(TypeName::Named { name, params }))
    }
}

// Parse an unnamed (tuple) type like () or (bool, Foo, Bar<T>).
fn parse_unnamed_into_type_name<'a>(input: &mut StrTokens<'a>) -> Option<Result<TypeName<'a>, ParseError>> {
    if !input.token('(') {
        return None
    }

    let params = match parse_comma_separated_type_names(input) {
        Ok(params) => params,
        Err(err) => return Some(Err(err))
    };

    if !input.token(')') {
        let loc = input.location().offset();
        Some(Err(ParseError::new_at(ParseErrorKind::ClosingParenMissing, loc)))
    } else {
        Some(Ok(TypeName::Unnamed { params }))
    }
}

// Parse a fixed length array like [Foo; 32].
fn parse_array_into_type_name<'a>(input: &mut StrTokens<'a>) -> Option<Result<TypeName<'a>, ParseError>> {
    if !input.token('[') {
        return None
    }

    skip_whitespace(input);
    let param = match parse_type_name(input) {
        Ok(param) => param,
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
        Some(Ok(TypeName::Array { param: Box::new(param), length }))
    }
}

// Parse a list of type names like Foo,Bar,usize. An empty list is allowed.
fn parse_comma_separated_type_names<'a>(input: &mut StrTokens<'a>) -> Result<Vec<TypeName<'a>>, ParseError> {
    skip_whitespace(input);
    let params = input.sep_by(
        |toks| try_parse_type_name(toks),
        |toks| {
            toks.surrounded_by(
                |toks| toks.token(','),
                |toks| skip_whitespace(toks)
            )
        }
    ).collect();
    skip_whitespace(input);

    params
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

    fn assert_parse(input: &str, type_name: TypeName<'_>) {
        let tn = match TypeName::parse(input) {
            Ok(tn) => tn,
            Err(e) => panic!("parsing '{input}' into {type_name:?} failed: {e}")
        };

        assert_eq!(tn, type_name, "parsing '{input}' into {type_name:?} failed: mismatch");
    }

    #[test]
    fn parsing_named_types_works() {
        assert_parse("Foo", TypeName::named("Foo"));
        assert_parse("Foo<>", TypeName::named("Foo"));
        assert_parse("Bar<u32>", TypeName::named_with_param("Bar", TypeName::named("u32")));
        assert_parse(
            "Bar<u32, Foo<bool>>",
            TypeName::named_with_params(
                "Bar",
                vec![
                    TypeName::named("u32"),
                    TypeName::named_with_param("Foo", TypeName::named("bool"))
                ]
            )
        );
        assert_parse(
            "Bar<u32,bool,   i64>",
            TypeName::named_with_params(
                "Bar",
                vec![
                    TypeName::named("u32"),
                    TypeName::named("bool"),
                    TypeName::named("i64"),
                ]
            )
        );
    }

    #[test]
    fn parsing_unnamed_tuple_types_works() {
        assert_parse("()", TypeName::unnamed(vec![]));
        assert_parse("(  )", TypeName::unnamed(vec![]));
        assert_parse("(bool,    i32,Bar<Wibble>, ())", TypeName::unnamed(vec![
            TypeName::named("bool"),
            TypeName::named("i32"),
            TypeName::named_with_param("Bar", TypeName::named("Wibble")),
            TypeName::unnamed(vec![]),
        ]));
    }

    #[test]
    fn parsing_array_types_works() {
        assert_parse("[Bar ;   10]", TypeName::array(TypeName::named("Bar"), 10));
        assert_parse("[Bar;1]", TypeName::array(TypeName::named("Bar"), 1));
        assert_parse(
            "[Bar<Wibble>;1]",
            TypeName::array(TypeName::named_with_param("Bar", TypeName::named("Wibble")), 1)
        );
        assert_parse("[u8;32]", TypeName::array(TypeName::named("u8"), 32));
    }

    #[test]
    fn parsing_complex_nested_type_works() {
        assert_parse(
            "Foo<(Option<Wibble<[(u8, Bar);12],Compact<()>>>,bool)>",
            TypeName::named_with_param(
                "Foo",
                TypeName::unnamed(vec![
                    TypeName::named_with_param(
                        "Option",
                        TypeName::named_with_params(
                            "Wibble",
                            vec![
                                TypeName::array(
                                    TypeName::unnamed(vec![TypeName::named("u8"), TypeName::named("Bar")]),
                                    12
                                ),
                                TypeName::named_with_param("Compact", TypeName::unnamed(vec![]))
                            ]
                        )
                    ),
                    TypeName::named("bool")
                ])
            )
        )
    }
}