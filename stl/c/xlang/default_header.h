#ifndef __XLANG_DEFAULT_HEADER_H
#define __XLANG_DEFAULT_HEADER_H

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

inline static void __print_panic_message__(const char *msg,
                                           const char *line_col) {
  printf("Panicked at %s with: \"%s\"", line_col, msg);
}

#define slice_t(ty) char *

#define XLANG_NULL ((void *)0)

#endif