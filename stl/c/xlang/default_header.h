#ifndef __XLANG_DEFAULT_HEADER_H
#define __XLANG_DEFAULT_HEADER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#define slice_t(ty) char *

#define tuple_1_t(t_0)                                                         \
  struct {                                                                     \
    t_0 _0;                                                                    \
  }
#define tuple_2_t(t_0, t_1)                                                    \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
  }
#define tuple_3_t(t_0, t_1, t_2)                                               \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
  }
#define tuple_4_t(t_0, t_1, t_2, t_3)                                          \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
  }
#define tuple_5_t(t_0, t_1, t_2, t_3, t_4)                                     \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
  }
#define tuple_6_t(t_0, t_1, t_2, t_3, t_4, t_5)                                \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
  }
#define tuple_7_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6)                           \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
  }
#define tuple_8_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7)                      \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
  }
#define tuple_9_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8)                 \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
  }
#define tuple_10_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8, t_9)           \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
    t_9 _9;                                                                    \
  }
#define tuple_11_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8, t_9, t_10)     \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
    t_9 _9;                                                                    \
    t_10 _10;                                                                  \
  }
#define tuple_12_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8, t_9, t_10,     \
                   t_11)                                                       \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
    t_9 _9;                                                                    \
    t_10 _10;                                                                  \
    t_11 _11;                                                                  \
  }
#define tuple_13_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8, t_9, t_10,     \
                   t_11, t_12)                                                 \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
    t_9 _9;                                                                    \
    t_10 _10;                                                                  \
    t_11 _11;                                                                  \
    t_12 _12;                                                                  \
  }
#define tuple_14_t(t_0, t_1, t_2, t_3, t_4, t_5, t_6, t_7, t_8, t_9, t_10,     \
                   t_11, t_12, t_13)                                           \
  struct {                                                                     \
    t_0 _0;                                                                    \
    t_1 _1;                                                                    \
    t_2 _2;                                                                    \
    t_3 _3;                                                                    \
    t_4 _4;                                                                    \
    t_5 _5;                                                                    \
    t_6 _6;                                                                    \
    t_7 _7;                                                                    \
    t_8 _8;                                                                    \
    t_9 _9;                                                                    \
    t_10 _10;                                                                  \
    t_11 _11;                                                                  \
    t_12 _12;                                                                  \
    t_13 _13;                                                                  \
  }

#define XLANG_NULL ((void *)0)

#endif