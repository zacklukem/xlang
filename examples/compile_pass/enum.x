
-- Generates:
-- ```
-- enum Maybe_k {
--     Maybe_Just_k,
--     Maybe_Nothing_k,
-- }
--
-- struct Maybe_i32 {
--     Maybe_k kind;
--     union {
--         tuple_i32_t Just;
--     };
-- }
--
-- Maybe_i32 Maybe_Just_i32(i32 _0) {
--     Maybe_i32 out;
--     out.kind = Maybe_Just_k;
--     out.Just = (tuple_i32_t){_0};
--     return out;
-- }
-- // ...
--
-- struct Maybe_i64 {
--     Maybe_k kind;
--     union {
--         tuple_i64_t Just;
--     } value;
-- }
-- ```
enum<T> Maybe {
    Just(T),
    Nothing,
}

fun main() -> i32 {
    let value = Maybe::Just::<i32>(1234);
    let value2 = Maybe::Just::<i64>(1234);
}
