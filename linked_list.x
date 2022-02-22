fun free(ptr: *void) {}
fun panic(msg: *[]u8) {}
fun alloc(size: usize) -> *void {}

struct List {
    head: *Node,
}

struct Node {
    data: i32,
    next: *Node,
}

fun List::len(*self) -> usize {
    if self.head == null {
        return 0;
    } else {
        return self.head.len();
    }
}

fun Node::len(*self) -> usize {
    if self == null {
        return 0;
    } else {
        return self.next.len() + 1;
    }
}

fun List::reverse(*self) {
    let prev = null as *Node;
    let node = self.head;
    let next = null as *Node;
    while node != null{
        next = node.next;
        node.next = prev;
        prev = node;
        node = next;
    }
    self.head = prev;
}

fun List::push_front(*self, val: i32) {
    self.head = box Node of {
        data: val,
        next: self.head,
    };
}

fun List::push_back(*self, val: i32) {
    self.head.push_back(val);
}

fun Node::push_back(*self, val: i32) {
    if self.next == null {
        self.next = box Node of {
            data: val,
            next: null,
        };
    } else {
        self.next.push_back(val);
    }
}

fun List::pop_back(*self) -> i32 {
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

fun Node::pop_back(*self) -> i32 {
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

fun List::pop_front(*self) -> i32 {
    let out = self.head.data;
    let old_head = self.head;
    self.head = self.head.next;
    old_head.free();
    return out;
}

fun List::nth(*self, idx: usize) -> i32 {
    self.head.nth(idx);
}

fun Node::nth(*self, idx: usize) -> i32 {
    if self == null {
        panic("Out of range");
    } else if idx == 0 {
        return self.data;
    } else {
        return self.next.nth(idx - 1);
    }
}

fun Node::free(*self) {
    self.next.free();
    free(self);
}
