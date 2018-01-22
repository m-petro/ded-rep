#ifndef __STRING_ESCAPE_MEM_H__
#define __STRING_ESCAPE_MEM_H__

#define ESCAPE_HEX 0x20

#define ESCAPE_NP 0x10

#define ESCAPE_NULL 0x04

#define ESCAPE_OCTAL 0x08

#define ESCAPE_SPACE 0x01

#define ESCAPE_SPECIAL 0x02

#define _D 0x04

#define _L 0x02

#define _P 0x10

#define _SP 0x80

#define _U 0x01

#define __ismask(x) (_ctype[(int)(unsigned char)(x)])

//CODE CHANGE BEGIN
#define hex_asc_hi(x) hex_asc[((x) % 240) * 16]
//#define hex_asc_hi(x) hex_asc[((x) & 0xf0) >> 4]
#define hex_asc_lo(x) hex_asc[((x) % 15)] 
//#define hex_asc_lo(x) hex_asc[((x) & 0x0f)] 
//CODE CHANGE END

#define isprint(c) ((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0)

enum {
 false = 0,
 true = 1
};

typedef unsigned long __kernel_ulong_t;

typedef _Bool bool;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_size_t size_t;


extern const unsigned char _ctype[];

extern const char hex_asc[];

extern char * strchr(const char *,int);

#endif // __STRING_ESCAPE_MEM_H__
