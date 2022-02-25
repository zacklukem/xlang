use crate::ty::{AdtType, Ty, TyCtx, TyKind};

pub fn replace_generics<'ty>(
    ctx: TyCtx<'ty>,
    ty: Ty<'ty>,
    generics: &Vec<(String, Ty<'ty>)>,
) -> Ty<'ty> {
    use TyKind::*;

    match ty.0 .0 {
        Param(val) => match generics.iter().find(|(pn, _)| pn == val) {
            Some((_, ty)) => *ty,
            None => ty,
        },
        Pointer(kind, inner) => {
            let inner = replace_generics(ctx, *inner, generics);
            ctx.int(Pointer(kind.clone(), inner))
        }
        Lhs(inner) => {
            let inner = replace_generics(ctx, *inner, generics);
            ctx.int(Lhs(inner))
        }
        SizedArray(size, inner) => {
            let inner = replace_generics(ctx, *inner, generics);
            ctx.int(SizedArray(*size, inner))
        }
        UnsizedArray(inner) => {
            let inner = replace_generics(ctx, *inner, generics);
            ctx.int(UnsizedArray(inner))
        }
        Range(inner) => {
            let inner = replace_generics(ctx, *inner, generics);
            ctx.int(Range(inner))
        }

        Tuple(tys) => {
            let tys: Vec<Ty<'ty>> = tys
                .iter()
                .map(|ty| replace_generics(ctx, *ty, generics))
                .collect();
            ctx.int(Tuple(tys))
        }
        Fun(params, ret) => {
            let ret = replace_generics(ctx, *ret, generics);
            let params: Vec<Ty<'ty>> = params
                .iter()
                .map(|ty| replace_generics(ctx, *ty, generics))
                .collect();
            ctx.int(Fun(params, ret))
        }
        Adt(AdtType {
            def_id,
            path,
            ty_params,
        }) => {
            let ty_params: Vec<Ty<'ty>> = ty_params
                .iter()
                .map(|ty| replace_generics(ctx, *ty, generics))
                .collect();
            ctx.int(Adt(AdtType {
                def_id: *def_id,
                path: path.clone(),
                ty_params,
            }))
        }

        Primitive(_) | Err | Unknown => ty,
    }
}
