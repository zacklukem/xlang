
enum<T> Maybe {
    Some(T),
    None,
}

enum<T> Stuff {
    Double(T, T),
    Single(T),
}

fun main() -> i32 {
    let value = Stuff::Double::<i32>(1234, 1234);
    let something = Maybe::None::<i32>();
    case value {
    | Stuff::Double(a, b) ->
        something = Maybe::Some::<i32>(8);
    | Stuff::Single(a) ->
        ret 5;
    }

    case something {
    | Maybe::Some(a) ->
        if a == 8 {
            ret 0;
        } else {
            ret 2;
        }
    | Maybe::None ->
        ret 4;
    }
    ret 3;
}
