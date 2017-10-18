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

/*@ axiomatic HexToBin {
    logic integer hex_to_bin(integer ch);
    axiom A0: hex_to_bin('0') == 0; 
    axiom A1: hex_to_bin('1') == 1; 
    axiom A2: hex_to_bin('2') == 2;
    axiom A3: hex_to_bin('3') == 3;
    axiom A4: hex_to_bin('4') == 4; 
    axiom A5: hex_to_bin('5') == 5;
    axiom A6: hex_to_bin('6') == 6; 
    axiom A7: hex_to_bin('7') == 7;
    axiom A8: hex_to_bin('8') == 8;
    axiom A9: hex_to_bin('9') == 9;
    axiom AA: hex_to_bin('a') == hex_to_bin('A') == 10;
    axiom AB: hex_to_bin('b') == hex_to_bin('B') == 11;
    axiom AC: hex_to_bin('c') == hex_to_bin('C') == 12;
    axiom AD: hex_to_bin('d') == hex_to_bin('D') == 13;
    axiom AE: hex_to_bin('e') == hex_to_bin('E') == 14;
    axiom AF: hex_to_bin('f') == hex_to_bin('F') == 15;
    }
 */

/*@ predicate isxdigit(integer c) = isdigit(c)        ||
                                    ('a' <= c <= 'f') ||
                                    ('A' <= c <= 'F');
*/
/*@ predicate isdigit(integer c)  = '0' <= c <= '9';

*/


/* assigns \nothing;
    behavior to_digit:
        assumes isxdigit(ch);
        ensures 0 <= \result <= 15;
        ensures \result == hex_to_bin(ch);
    behavior fail:
        assumes !isxdigit(ch);
        ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */

extern int hex_to_bin(char ch);


//@ predicate isodigit(integer c) = '0' <= c <= '7';
//@ ensures \result <==> isodigit(c);

static inline int isodigit(const char c);

#endif // __STRING_UNESCAPE_H__
