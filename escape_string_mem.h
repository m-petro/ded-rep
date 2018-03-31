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
// CHANGED CODE BEGIN
#define hex_asc_hi(x) hex_asc[((x) % 240) / 16]
  // original - #define hex_asc_hi(x) hex_asc[((x) & 0xf0) >> 4] 
#define hex_asc_lo(x) hex_asc[((x) % 16)] 
  // original - #define hex_asc_lo(x) hex_asc[((x) & 0x0f)] 
// CHANGED CODE END
#define isprint(c) ((__ismask(c)&(_P|_U|_L|_D|_SP)) != 0)

enum {
 false = 0,
 true = 1
};

const char hex_asc[] = "0123456789abcdef";

typedef unsigned long __kernel_ulong_t;
typedef _Bool bool;
typedef __kernel_ulong_t __kernel_size_t;
typedef __kernel_size_t size_t;


extern const unsigned char _ctype[];


/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));
    lemma valid_str_shift1:
       \forall char *s;
          *s != '\0' &&
          valid_str(s) ==>
             valid_str(s+1);
    lemma valid_str_strend:
       \forall char *s;
          \valid(s) && *s == '\0' ==>
             valid_str(s);
    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));
    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_str(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';
    lemma strlen_at_null:
       \forall char* s;
          valid_str(s) ==> s[strlen(s)] == '\0';
    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_str(s) &&
          i <= strlen(s) ==>
          strlen(s+i) == strlen(s)-i;
    lemma strlen_shift_ex:
       \forall char *s, size_t i;
          valid_str(s) &&
          0 < i <= strlen(s) ==>
          strlen(s+i) < strlen(s);
    lemma strlen_shift1:
       \forall char *s;
          valid_str(s) && *s != '\0' ==>
          strlen(s) == 1 + strlen(s+1);
    lemma strlen_pointers:
       \forall char *s, *sc;
          valid_str(s)  &&
          valid_str(sc) &&
          \base_addr(s) == \base_addr(sc) &&
          s <= sc &&
          (\forall integer i; 0 <= i <= sc - s ==> s[i] != '\0') ==>
             strlen(sc) <= strlen(s);
    lemma strlen_main:
       \forall char *s, size_t n;
       valid_str(s) &&
       s[n] == '\0' &&
       (\forall integer i; 0 <= i < n ==> s[i] != '\0') ==>
           strlen(s) == n;
    lemma valid_str_shiftn:
       \forall char *s, integer i;
          valid_str(s) &&
          (0 <= i < strlen(s)) ==>
             valid_str(s+i);
    }
 */

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \result == strlen(s);
    ensures s[\result] == '\0';
    ensures \forall integer i; 0 <= i < \result ==> s[i] != '\0';
*/

size_t strlen(const char *s);

/*@ axiomatic Strchr {
    logic char *strchr(char *str, char c) =
       *str == c ? str : ((*str == '\0') ? (char *) \null : strchr(str+1, c));
    lemma mem:
       \forall char *str, c;
       valid_str(str) ==>
          (str <= strchr(str, c) <= str + strlen(str)) ^^
          strchr(str, c) == \null;
    lemma iter_one:
       \forall char *str, c;
       valid_str(str) && *str != c && *str != '\0' ==>
          strchr(str, c) == strchr(str+1, c);
    lemma res:
       \forall char *str, c;
       valid_str(str) ==>
          strchr(str, c) == \null ^^ *strchr(str, c) == c;
    lemma at_end_zero:
       \forall char *str, c;
       \valid(str) && *str == '\0' ==>
          strchr(str, c) == \null;
    lemma at_end_char:
       \forall char *str, c;
       \valid(str) && *str == c ==>
          strchr(str, c) == str;
    lemma defn:
       \forall char *str, c, integer i;
       valid_str(str) && 0 <= i <= strlen(str) &&
       (\forall integer j; 0 <= j < i ==> str[j] != c) &&
       str[i] == c ==>
          str + i == strchr(str, c);
    lemma skipped:
       \forall char *str, c, integer i;
       valid_str(str) &&
       0 <= i < strchr(str, c) - str <= strlen(str) ==>
          str[i] != c;
    }
*/

/*@ requires valid_str(s);
    assigns \nothing;
    ensures \result == strchr(s, (char %) c);
    behavior not_exists:
       assumes \forall char *p; s <= p <= s + strlen(s) ==> *p != (char %) c;
       ensures \result == \null;
    behavior exists:
       assumes \exists char *p; s <= p <= s + strlen(s) && *p == (char %) c;
       ensures s <= \result <= s + strlen(s);
       ensures *\result == (char %) c;
       ensures \forall char *p; s <= p < \result ==> *p != (char %) c;
    complete behaviors;
    disjoint behaviors;
 */

extern char * strchr(const char *s, int c);

#endif // __STRING_ESCAPE_MEM_H__
