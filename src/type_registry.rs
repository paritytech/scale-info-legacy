use std::collections::HashMap;
use crate::type_desc::TypeDesc;
use crate::type_name::TypeName;
use scale_type_resolver::{TypeResolver,ResolvedTypeVisitor};

#[derive(Debug,derive_more::Display)]
pub enum TypeRegistryError {

}

pub struct TypeRegistry {
    types: HashMap<String, TypeDesc>,
}

impl TypeResolver for TypeRegistry {
    type TypeId = TypeName;
    type Error = TypeRegistryError;

    fn resolve_type<'this, V: ResolvedTypeVisitor<'this, TypeId = Self::TypeId>>(
        &'this self,
        type_id: &Self::TypeId,
        visitor: V,
    ) -> Result<V::Value, Self::Error> {
        todo!()
    }
}