extern fun check(expr: bool);

fun main() -> i32 {
    check(if false then false else true);
    let n = if true then 0 else 1;
    ret n;
}