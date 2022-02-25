# X-Lang

- [X-Lang](#x-lang)
  - [Architecture](#architecture)
  - [Name Mangling](#name-mangling)
  - [Example](#example)

The name is probably already taken by somebody...

X-Lang is a programming language that compiles into C code.  It is a hobby project
with the design goal of being a low-level language like C, but with generics and
some nice syntax sugars.  The generics are designed to be simple and generate
symbols that are usable from C.

Written in Rust (what X-Lang wishes it could be)

## Architecture

Compilation is divided into the following parts:

1. **Parsing**:

    An ast is generated from the source code using a parser generator (lalrpop)

1. **IR Generation**

    Typed IR is generated from the AST.  The typed IR has minimal type inference
    for let statements and member functions but otherwise types must be stated
    explicitly.

1. **Monomorphization**

    The IR is walked starting at the mono nodes (functions and structs without
    generics) and each referenced function and type is then added to a list
    of top level symbols with explicit types.

1. **Code Generation**

    I kinda just threw this together because I wanted to see some hello world
    so it just writes some text to a file and has lots of bugs.  Will rewrite
    from scratch....... eventually........

## Name Mangling

In X-Lang, "mangled" names are designed to be consistent (WIP) and human readable.
For example, a structure called `List` with a single type parameter `i32`
will be monomorphized and result in a C typedef named: `List_i32_t`.

Additionally, namespaces are mangled in a readable fashion, for example
`List::push` becomes `List_push`.

## Example

The following is code for a basic resizable vector:
```
extern fun realloc(ptr: *void, size: usize) -> *void;
extern fun malloc(size: usize) -> *void;
extern fun<T> sizeof() -> usize;
extern fun check(expr: bool);
extern fun free(ptr: *void);

fun<T> resize(ptr: **T, len: usize) {
    *ptr = realloc(*ptr, len * sizeof::<T>()) as *T;
}

fun<T> allocate(len: usize) -> *T {
    ret malloc(len * sizeof::<T>()) as *T;
}

struct<T> Vec {
    data: *T,
    len: usize,
    cap: usize,
}

fun<T> Vec::<T>::new() -> Vec::<T> {
    ret Vec::<T> of {
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
    ret 0;
}

```

This generates the following C code (ran through clang-format):

```c
/* vector.h */
#pragma once
#include <xlang/default_header.h>

typedef struct Vec_i32 Vec_i32_t;

int32_t main();
void *realloc(void *ptr, size_t size);
void free(void *ptr);
void resize_i32(int32_t **ptr, size_t len);
void check(bool expr);
void Vec_push_i32(Vec_i32_t *self, int32_t data);
size_t sizeof_i32();
void *malloc(size_t size);
Vec_i32_t Vec_new_i32();
int32_t *allocate_i32(size_t len);

struct Vec_i32 {
  size_t len;
  size_t cap;
  int32_t *data;
};
```

```c
/* vector.c */
#include "vector.h"
int32_t main() {
  Vec_i32_t vec_0;
  int32_t i_1;
  {
    (vec_0 = Vec_new_i32());

    check(vec_0.len == (size_t)(0));
    check(vec_0.cap == (size_t)(8));
    (i_1 = (int32_t)(0));

  while_2_continue:
    while ((i_1 < (int32_t)(8))) {
      Vec_push_i32((&vec_0), i_1);
      (i_1 += (int32_t)(1));
    }

  while_2_break:
    check(vec_0.len == (size_t)(8));
    check(vec_0.cap == (size_t)(8));
    Vec_push_i32((&vec_0), (int32_t)(123));
    check(vec_0.len == (size_t)(9));
    check(vec_0.cap == (size_t)(16));
    return (int32_t)(0);
  }
}
void resize_i32(int32_t **ptr, size_t len) {
  {
    ((*ptr) = (int32_t *)(realloc((void *)((*ptr)), (len * sizeof(int32_t)))));
  }
}
void Vec_push_i32(Vec_i32_t *self, int32_t data) {
  {
    if (self->len == self->cap) {
      (self->cap += (size_t)(8));
      resize_i32((&self->data), self->cap);
    }

    (self->data[self->len] = data);
    (self->len += (size_t)(1));
  }
}
Vec_i32_t Vec_new_i32() {
  {
    return ((Vec_i32_t){.data = allocate_i32((size_t)(8)),
                        .len = (size_t)(0),
                        .cap = (size_t)(8)});
  }
}
int32_t *allocate_i32(size_t len) {
  { return (int32_t *)(malloc((len * sizeof(int32_t)))); }
}
```
