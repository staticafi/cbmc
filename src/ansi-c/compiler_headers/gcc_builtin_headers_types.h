// clang-format off
typedef void ** __builtin_va_list;
typedef void ** __builtin_ms_va_list;

typedef int    __gcc_m64   __attribute__ ((__vector_size__ (8), __may_alias__));

typedef char   __gcc_v8qi  __attribute__ ((__vector_size__ (8)));
typedef char   __gcc_v16qi __attribute__ ((__vector_size__ (16)));
typedef char   __gcc_v32qi __attribute__ ((__vector_size__ (32)));
typedef char   __gcc_v64qi __attribute__ ((__vector_size__ (64)));
typedef int    __gcc_v2si  __attribute__ ((__vector_size__ (8)));
typedef int    __gcc_v4si  __attribute__ ((__vector_size__ (16)));
typedef int    __gcc_v8si  __attribute__ ((__vector_size__ (32)));
typedef int    __gcc_v16si  __attribute__ ((__vector_size__ (64)));
typedef int    __gcc_v256si  __attribute__ ((__vector_size__ (1024)));
typedef short  __gcc_v4hi  __attribute__ ((__vector_size__ (8)));
typedef short  __gcc_v8hi  __attribute__ ((__vector_size__ (16)));
typedef short  __gcc_v16hi __attribute__ ((__vector_size__ (32)));
typedef short  __gcc_v32hi __attribute__ ((__vector_size__ (64)));
typedef __CPROVER_Float16  __gcc_v8hf  __attribute__ ((__vector_size__ (16)));
typedef __CPROVER_Float16  __gcc_v16hf  __attribute__ ((__vector_size__ (32)));
typedef __CPROVER_Float16  __gcc_v32hf  __attribute__ ((__vector_size__ (64)));
typedef float  __gcc_v2sf  __attribute__ ((__vector_size__ (8)));
typedef float  __gcc_v4sf  __attribute__ ((__vector_size__ (16)));
typedef float  __gcc_v8sf  __attribute__ ((__vector_size__ (32)));
typedef float  __gcc_v16sf  __attribute__ ((__vector_size__ (64)));
typedef double __gcc_v2df  __attribute__ ((__vector_size__ (16)));
typedef double __gcc_v4df  __attribute__ ((__vector_size__ (32)));
typedef double __gcc_v8df  __attribute__ ((__vector_size__ (64)));
typedef long long __gcc_v1di __attribute__ ((__vector_size__ (8)));
typedef long long __gcc_v2di __attribute__ ((__vector_size__ (16)));
typedef long long __gcc_v4di __attribute__ ((__vector_size__ (32)));
typedef long long __gcc_v8di __attribute__ ((__vector_size__ (64)));
typedef unsigned short __gcc_v32uhi __attribute__ ((__vector_size__ (64)));
typedef unsigned int __gcc_v4usi __attribute__ ((__vector_size__ (16)));
typedef unsigned int __gcc_v8usi __attribute__ ((__vector_size__ (32)));
typedef unsigned int __gcc_v16usi  __attribute__ ((__vector_size__ (64)));
typedef unsigned long long __gcc_di;
typedef unsigned long long __gcc_v2udi __attribute__ ((__vector_size__ (16)));
typedef unsigned long long __gcc_v4udi __attribute__ ((__vector_size__ (32)));
typedef unsigned long long __gcc_v8udi __attribute__ ((__vector_size__ (64)));

enum __gcc_atomic_memmodels {
  __ATOMIC_RELAXED, __ATOMIC_CONSUME, __ATOMIC_ACQUIRE, __ATOMIC_RELEASE, __ATOMIC_ACQ_REL, __ATOMIC_SEQ_CST
};

typedef unsigned char __tile __attribute__ ((__vector_size__ (1024)));
// clang-format on
