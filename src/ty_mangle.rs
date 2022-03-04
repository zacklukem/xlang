use crate::codegen::mangle_path;
use crate::ty::*;
use std::fmt::Write;

pub fn mangle_ty_vec(vec: &[Ty<'_>]) -> String {
    let mut string = String::new();
    for ty in vec {
        string += "_";
        ty.mangle_write(&mut string).unwrap();
    }
    string
}

impl std::fmt::Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PrimitiveType::*;
        let st = match self {
            Void => "void",
            Bool => "bool",
            F64 => "f64",
            F32 => "f32",
            I64 => "i64",
            I32 => "i32",
            I16 => "i16",
            I8 => "i8",
            USize => "usize",
            U64 => "u64",
            U32 => "u32",
            U16 => "u16",
            U8 => "u8",
            Integer => "integer",
        };
        f.write_str(st)
    }
}

impl<'ty> Ty<'ty> {
    pub fn mangle(self) -> String {
        let mut string = String::new();
        self.mangle_write(&mut string).unwrap();
        string
    }

    pub fn mangle_write<T>(self, f: &mut T) -> std::fmt::Result
    where
        T: Write,
    {
        use TyKind::*;
        match self.0 .0 {
            Primitive(pt) => write!(f, "{}", pt),
            Param(ty_param) => f.write_str(ty_param),
            Pointer(PointerType::Star, inner) => {
                inner.mangle_write(f)?;
                f.write_str("_ptr")
            }
            Pointer(PointerType::StarMut, inner) => {
                inner.mangle_write(f)?;
                f.write_str("_ptr")
            }
            Tuple(types) => {
                f.write_str("tuple")?;
                for ty in types {
                    f.write_str("_")?;
                    ty.mangle_write(f)?;
                }
                f.write_str("_")
            }
            Fun(params, ret) => {
                f.write_str("fun")?;
                for ty in params {
                    f.write_str("_")?;
                    ty.mangle_write(f)?;
                }
                f.write_str("_to_")?;
                ret.mangle_write(f)
            }
            SizedArray(size, inner) => {
                write!(f, "{}_", size)?;
                inner.mangle_write(f)?;
                f.write_str("_arr")
            }
            UnsizedArray(inner) => {
                inner.mangle_write(f)?;
                f.write_str("_arr")
            }
            Range(inner) => {
                inner.mangle_write(f)?;
                f.write_str("_range")
            }
            Adt(AdtType {
                def_id: _,
                path,
                ty_params,
            }) => {
                write!(f, "{}", mangle_path(path))?;
                for ty in ty_params {
                    f.write_str("_")?;
                    ty.mangle_write(f)?;
                }
                Ok(())
            }
            Err => f.write_str("ERR_TY"),
            TyVar(_) => panic!(),
        }
    }
}
