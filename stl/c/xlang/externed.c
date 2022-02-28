#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void check_check(bool value) { assert(value); }

void *mem_malloc(size_t size) { return malloc(size); }

void *mem_realloc(void *ptr, size_t size) { return realloc(ptr, size); }

void mem_free(void *ptr) { free(ptr); }

void print_int(int32_t value) { printf("%d\n", value); }