fun free(ptr: *void) {}
fun panic(msg: *[]u8) {}
fun alloc(size: usize) -> *void {}
fun assert(expr: bool) {}

fun main() {
    let list = List::new::<i64>();
    assert(list.len() == 0);
    list.push_back(3);
    assert(list.len() == 1);
    assert(list.pop_back() == 3);
}

struct<T> Word {
    head: *Node::<T>,
}

struct<T> List {
    head: *Node::<T>,
}

struct<T> Node {
    data: T,
    next: *Node::<T>,
}

fun<T> List::<T>::new() -> List::<T> {
    return List::<T> of { head: null, };
}

fun<T> List::<T>::len(*self) -> usize {
    let a = List::len::<T>;
    if self.head == null {
        return 0;
    } else {
        return self.head.len();
    }
}

fun<K> Node::<K>::len(*self) -> usize {
    if self == null {
        return 0;
    } else {
        self.next = self;
        return self.next.len() + 1;
    }
}

fun<T> List::<T>::reverse(*self) {
    let prev = null as *Node::<T>;
    let node = self.head;
    let next = null as *Node::<T>;
    while node != null{
        next = node.next;
        node.next = prev;
        prev = node;
        node = next;
    }
    self.head = prev;
}

fun<T> List::<T>::push_front(*self, val: T) {
    self.head = box Node::<T> of {
        data: val,
        next: self.head,
    };
}

fun<T> List::<T>::push_back(*self, val: T) {
    self.head.push_back(val);
}

fun<T> Node::<T>::push_back(*self, val: T) {
    if self.next == null {
        self.next = box Node::<T> of {
            data: val,
            next: null,
        };
    } else {
        self.next.push_back(val);
    }
}

fun<T> List::<T>::pop_back(*self) -> T {
    if self.head == null {
        panic("Popped on empty list");
    } else if self.head.next == null {
        let out = self.head.data;
        self.head.free();
        self.head = null;
        return out;
    } else {
        return self.head.pop_back();
    }
}

fun<T> Node::<T>::pop_back(*self) -> T {
    if self.next == null {
        panic("Popped on empty list");
    } else if self.next.next == null {
        let out = self.next.data;
        self.next.free();
        self.next = null;
        return out;
    } else {
        return self.next.pop_back();
    }
}

fun<T> List::<T>::pop_front(*self) -> T {
    let out = self.head.data;
    let old_head = self.head;
    self.head = self.head.next;
    old_head.free();
    return out;
}

fun<T> List::<T>::nth(*self, idx: usize) -> T {
    self.head.nth(idx);
}

fun<T> Node::<T>::nth(*self, idx: usize) -> T {
    if self == null {
        panic("Out of range");
    } else if idx == 0 {
        return self.data;
    } else {
        return self.next.nth(idx - 1);
    }
}

fun<T> Node::<T>::free(*self) {
    self.next.free();
    free(self);
}
