
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

-- Generates:
--
--
-- i32 main() {
--     // ...
--     value = Maybe_Just_i32(1234);
--     switch value.kind {
--     case Maybe_Just_k:
--         val = value.Just._0;
--         check(val == 1234);
--         break;
--     case Maybe_Nothing_k:
--         check(false);
--         break;
--     }
--     ret 0;
-- }
fun main() -> i32 {
    let value = Maybe::Just::<i32>(1234);
    -- case value {
    -- | Maybe::Just(val) ->
    --     check(val == 1234);
    --     ret 0;
    -- | Maybe::Nothing ->
    --     check(false);
    --     ret 1;
    -- }
    ret 0;
}
