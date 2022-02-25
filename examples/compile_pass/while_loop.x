extern fun print_int(n: i32);
extern fun check(expr: bool);

fun main() -> i32 {
    let a = 1;
    let b = 1;
    while b < 9999999 {
        print_int(b);
        let temp = b;
        b = a + b;
        a = temp;
        if b == 4 {
            break;
        }
    }
    return 0;
}