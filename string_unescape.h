#ifndef __STRING_UNESCAPE_H__
#define __STRING_UNESCAPE_H__

#define UNESCAPE_HEX 0x04

#define UNESCAPE_OCTAL 0x02

#define UNESCAPE_SPACE 0x01

#define UNESCAPE_SPECIAL 0x08

enum {
 false = 0,
 true = 1
};

typedef unsigned long __kernel_ulong_t;

typedef _Bool bool;

typedef unsigned char u8;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;
//------------------------------------------------------------------------------

extern int hex_to_bin(char ch);

static inline int isodigit(const char c);

#endif // __STRING_UNESCAPE_H__
