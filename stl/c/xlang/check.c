#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

void check(bool value) { assert(value); }

void print_int(int32_t value) { printf("%d\n", value); }