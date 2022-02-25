extern fun realloc(ptr: *void, size: usize) -> *void;
extern fun malloc(size: usize) -> *void;
extern fun<T> sizeof() -> usize;
extern fun check(expr: bool);
extern fun free(ptr: *void);

fun<T> resize(ptr: **T, len: usize) {
    *ptr = realloc(*ptr, len * sizeof::<T>()) as *T;
}

fun<T> allocate(len: usize) -> *T {
    return malloc(len * sizeof::<T>()) as *T;
}

struct<T> Vec {
    data: *T,
    len: usize,
    cap: usize,
}

fun<T> Vec::<T>::new() -> Vec::<T> {
    return Vec::<T> of {
        data: allocate::<T>(8),
        len: 0,
        cap: 8,
    };
}

fun<T> Vec::<T>::push(*self, data: T) {
    if self.len == self.cap {
        self.cap += 8;
        resize::<T>(&self.data, self.cap);
    }
    self.data[self.len] = data;
    self.len += 1;
}

fun<T> Vec::<T>::free(*self) {
    free(self.data);
}

fun main() -> i32 {
    let vec = Vec::new::<i32>();
    check(vec.len == 0);
    check(vec.cap == 8);
    let i = 0;
    while i < 8 {
        vec.push(i);
        i+=1;
    }
    check(vec.len == 8);
    check(vec.cap == 8);
    vec.push(123);
    check(vec.len == 9);
    check(vec.cap == 16);
    return 0;
}
