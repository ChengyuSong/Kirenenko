//===-- dfsan.h -------------------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file is a part of DataFlowSanitizer.
//
// Private DFSan header.
//===----------------------------------------------------------------------===//

#ifndef DFSAN_H
#define DFSAN_H

#include "sanitizer_common/sanitizer_internal_defs.h"
#include "dfsan_platform.h"
#include <stdio.h>

using __sanitizer::uptr;
using __sanitizer::u64;
using __sanitizer::u32;
using __sanitizer::u16;
using __sanitizer::u8;

#define AOUT(...)                                       \
  do {                                                  \
    if (1)  {                                           \
      Printf("[RT] (%s:%d) ", __FUNCTION__, __LINE__);  \
      Printf(__VA_ARGS__);                              \
    }                                                   \
  } while(false)

// Copy declarations from public sanitizer/dfsan_interface.h header here.
typedef u32 dfsan_label;

struct dfsan_label_info {
  dfsan_label l1;
  dfsan_label l2;
  u8 op;
  u8 size;
  u64 op1;
  u64 op2;
};

#ifndef PATH_MAX
# define PATH_MAX 4096
#endif
#define CONST_OFFSET 1

struct taint_file {
  char filename[PATH_MAX];
  int fd;
  off_t offset;
  dfsan_label label;
  long size;
  int is_utmp;
};

extern "C" {
void dfsan_add_label(dfsan_label label, u8 op, void *addr, uptr size);
void dfsan_set_label(dfsan_label label, void *addr, uptr size);
dfsan_label dfsan_read_label(const void *addr, uptr size);
void dfsan_store_label(dfsan_label l1, void *addr, uptr size);
dfsan_label dfsan_union(dfsan_label l1, dfsan_label l2, u8 op, u8 size);
dfsan_label dfsan_create_label(void);

// taint source
void taint_set_file(const char *filename, int fd);
int taint_get_file(int fd);
void taint_close_file(int fd);
int is_taint_file(const char *filename);

// taint source utmp
off_t get_utmp_offset(void);
void set_utmp_offset(off_t offset);
int is_utmp_taint(void);
}  // extern "C"

template <typename T>
void dfsan_set_label(dfsan_label label, T &data) {  // NOLINT
  dfsan_set_label(label, (void *)&data, sizeof(T));
}

namespace __dfsan {

void InitializeInterceptors();

inline dfsan_label *shadow_for(void *ptr) {
  return (dfsan_label *) ((((uptr) ptr) & ShadowMask()) << 2);
}

inline const dfsan_label *shadow_for(const void *ptr) {
  return shadow_for(const_cast<void *>(ptr));
}

struct Flags {
#define DFSAN_FLAG(Type, Name, DefaultValue, Description) Type Name;
#include "dfsan_flags.inc"
#undef DFSAN_FLAG

  void SetDefaults();
};

extern Flags flags_data;
inline Flags &flags() {
  return flags_data;
}

enum operators {
  // bitwise
  bvnot = 1,
  bvand = 26,
  bvor = 27,
  bvxor = 28,
  bvshl = 23,
  bvlshr = 24,
  bvashr = 25,
  // arithmetic
  bvneg = 2,
  bvadd = 11,
  bvsub = 13,
  bvmul = 15,
  bvudiv = 17,
  bvsdiv = 18,
  bvurem = 20,
  bvsrem = 21,
  // extend
  bvtrunc = 36,
  bvzext = 37,
  bvsext = 38,
  // load
  bvload = 3,
  bvconcat = 5,
  // extract
  bvextract = 4,
  // functions
  fmemcmp = 51,
  fcrc32 = 52
};

enum predicate {
  bveq,
  bvneq,
  bvslt,
  bvult,
  bvsle,
  bvule,
  bvsgt,
  bvugt,
  bvsge,
  bvuge
};

static inline bool is_commutative(unsigned char op) {
  switch(op) {
    case bvand:
    case bvor:
    case bvxor:
    case bvadd:
    case bvmul:
    case fmemcmp:
      return true;
    default:
      return false;
  }
}

}  // namespace __dfsan

#endif  // DFSAN_H
