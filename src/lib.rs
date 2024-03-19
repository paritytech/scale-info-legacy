//! This crate provides a type registry that is capable of storing and providing back information about
//! historic Substrate based types (ie those that are handed back in pre-V14 metadata).

#![deny(missing_docs)]

mod type_name;
mod type_desc;
mod type_registry;

/*
Thouhgts:

pub struct Registry;

// Basic (no default types given)
let mut registry = Registry::bare()

// Some type mappings to support:
Vec<T> => Sequence of elements of type T
Foo<A> => Struct like { hello: bool, other: A }
MyEnum<T, S> => Enum like { A(Bool), B(T), C(S) }
(A, B, C) => arbitrary tuples of any number of generics (prob a built-in thing).
[T; N] => arbitrary arrays (prob built in).
BTreeMap<K, V> => Sequence of elements of type (K, V)
MyInt => u32 (we can have plain aliases and such too).
Foo<E> => E (also plain type things like this).
path::to::SomeType<R> => we should support full type paths too.
Compact<Foo> => handle compact encoding.

// Some resolving things to support:
Vec<(ParaId,Option<(CollatorId,Retriable)>)> => complex nested resolving

// Resolving should line up generics and error if wrong number. Can substitute generics into
// the right places, and then communicate what the output shape is via `scale-type-resolver` stuff.
// When inserting types, _only_ generics are supported as params. Like defining types.

registry.insert("Vec", Ty::SequenceOf(Ty::Param("T")))
registry.insert("Foo", Ty::Struct(vec![ ("hello", Ty::Bool), ("other", Ty::Param("T")) ]))
registry.insert("MyEnum<T, S>", Ty::Enum(vec![ Variant::new("A", Ty::Bool).with_index(3), Variant::new("B", Ty::Param("T")), ... ]))
registry.insert("BTreeMap<K,V>", Ty::SequenceOf(Ty::TupleOf(vec![Ty::Param("K"), Ty::Param("V")])))
registry.insert("Compact<T>", Ty::Compact(Ty::Param("T")))
registry.insert("MyInt", Ty::U32)
registry.insert("MyArray", Ty::ArrayOf(Ty::U8, 32))
registry.insert("Foo<E>", Ty::Param("E"))
registry.insert("path::to::SomeType<R>", Ty::Param("R"))
registry.insert("MyAlias<T>", Ty::Alias("[T; 32]"))
    // simple aliases can just resolve the inner thing. alias with type params hmmmm.
    // maybe allow passing strings in and we can parse them (ie TryInto<Ty>):
    //   registry.insert("MyAlias<T>", "[T; 32]") // array
    //   registry.insert("MyAlias<T>", "[T]") // sequence of t
    //   registry.insert("Foo<T>", "struct { thing: bool, other: [u8; 32], more: (T, String) }") // struct
    //   registry.insert("Bar", "enum { A(bool), B { foo: usize, bar: u32 }, C }")
    // Instead of parsing strings we could provide a macro for this.
    // We also plan for Ty to impl a JSON format like what has been seen before.

// How to resolve something:
registry.resolve("Vec<(ParaId,Option<(CollatorId,Retriable)>)>")

1. Parse into TypeName::Named { name: "Vec", param_names: vec!["(ParaId,Option<(CollatorId,Retriable)>)"] )
   - Also can have:
       TypeName::Array { param_name: &str, length: usize }
       TypeName::Tuple { param_names: vec!["usize", "bool", "(Foo<T>, Bar<E>)"] }
   - This can hold refs to original string; no need for allocating too much I hope.
     (smallvec or whatever for param names maybe too; don't expect more than a few normally).
2. Internally look up the type with the given name.
   - registry.lookup_type_name("Vec") => &{ params: vec!["T"], desc: Ty::SequenceOf(Ty::Param("T")) }
   - We have 1 param too, so what we provided looks valid.
     - We have a sequence and we can map the param provided to T, recursively resolving that param when we get to it.







// We would prob provide some of these built-in things by default (tuples especially):
registry.insert("Vec<T>", Type::Sequence);

// What if A is already a known concrete type for instance? Or maybe it's impossible to eg give "Vec<u32>" or "(bool, u64)"
// when inserting type definitions in the first place, and everything is generic.
registry.insert("(A, B, C)", Type::TupleOf(vec![Type::Placeholder("A"), Type::Placeholder("B"), Type::Placeholder("C")]));
registry.insert("u32", Type::U32);
registry.insert("bool", Type::Bool);

// When we come to look up a type we always need to provide concrete types where generics would be.
registry.resolve("Vec<u32>")
// How to resolve this?
// 1. Break type into some description of it like `TypeName { name: "Vec", params: vec!["u32"] }`
// 2. Look up "Vec". Get back `Type::SequenceOf`


*/