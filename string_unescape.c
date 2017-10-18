#include "string_unescape.h"

/*@ requires \valid(src) && \valid(*src);
    requires \valid(dst) && \valid(*dst);
    requires **src == 'x' ==> \valid(*src + 1);
    requires isxdigit(*(*src + 1)) ==> \valid(*src + 2);
    behavior not_hex:
       assumes **src != 'x' ||
          (**src == 'x' && !isxdigit(*(*src + 1)));
       assigns \nothing;
       ensures \result == \false;
    behavior one_digit:
       assumes **src == 'x';
       assumes isxdigit(*(*src + 1));
       assumes !isxdigit(*(*src + 2));
       assigns **dst, *dst, *src;
       ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 2);
       ensures *(\old(*dst)) == hex_to_bin(*(*\old(src) + 1));
       ensures \result == \true;
   behavior two_digits:
       assumes **src == 'x';
       assumes isxdigit(*(*src + 1));
       assumes isxdigit(*(*src + 2));
       assigns **dst, *dst, *src;
       ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 3);
       ensures \result == \true;
   complete behaviors;
   disjoint behaviors;
*/
 
static bool unescape_hex(char **src, char **dst)
{
	char *p = *dst, *q = *src;
	int digit;
	u8 num;

	if (*q++ != 'x')
		return false;
		//@ assert q == *src + 1;

	num = digit = hex_to_bin(*q++);
	if (digit < 0)
		return false;
		//@ assert q == *src + 2;

	digit = hex_to_bin(*q);
	if (digit >= 0) {
		q++;
		//@ assert q == *src + 3;
		num = (num << 4) | digit;
	}
	*p = num;
	*dst += 1;
	//@ assert q == (*src + 2) || q == (*src + 3);
	*src = q;
	return true;
}

/*@ requires \valid(src) && \valid(*src);
    requires \valid(dst) && \valid(*dst);
    requires isodigit(**src) ==> \valid(*src + 1);
    requires isodigit(*(*src + 1)) ==> \valid(*src + 2);
    requires isodigit(*(*src + 2)) ==> \valid(*src + 3);
    behavior not_octal:
       assumes !isodigit(**src);
       assigns \nothing;
       ensures \result == \false;
    behavior one_digit:
       assumes isodigit(**src);
       assumes !isodigit(*(*src + 1));
       assigns **dst, *dst, *src;
       ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 1);
       ensures *(\old(*dst)) == (**\old(src));
       ensures \result == \true;
   behavior two_digits:
       assumes isodigit(**src);
       assumes isodigit(*(*src + 1));
       assumes !isodigit(*(*src + 2));
       assigns **dst, *dst, *src;
       ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 2);
       ensures *(\old(*dst)) == (**\old(src)) + 8 * (*(\old(*src + 1)));
       ensures \result == \true;
   behavior three_digits:
	   assumes isodigit(**src);
       assumes isodigit(*(*src + 1));
       assumes isodigit(*(*src + 2));
       assigns **dst, *dst, *src;
       ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 3);
       ensures *(\old(*dst)) == (**\old(src)) + 8 * (*(\old(*src + 1))) + 64 * (*(\old(*src + 2)));
       ensures \result == \true;
   complete behaviors;
   disjoint behaviors;
*/

static bool unescape_octal(char **src, char **dst)
{
	char *p = *dst, *q = *src;
	u8 num;

	if (isodigit(*q) == 0)
		return false;
	num = (*q++) & 7;
	
	//@ assert q == *src + 1;
	
	/*@ loop invariant 1 <= (q - *src) <= 3;
		loop variant (q - *src);
	*/ 
		
	while (num < 32 && isodigit(*q) && (q - *src < 3)) {
		num <<= 3;
		num += (*q++) & 7;

	}
	
	*p = num;
	*dst += 1;
	*src = q;
	return true;
}

/*@ axiomatic Un_Space {
    logic char unescape_space (integer ch);
	axiom N: unescape_space ('n') == '\n';
	axiom R: unescape_space ('r') == '\r';
	axiom T: unescape_space ('t') == '\t';	
	axiom V: unescape_space ('v') == '\v';
	axiom F: unescape_space ('f') == '\f';
    }
*/

/*@
	requires \valid (src) && \valid (dst) &&
			 \valid (*src) && \valid(*dst);
	assigns (**dst), *src, *dst;
    behavior is_space:
        assumes (**src) == 'n' || (**src) == 't' ||
				(**src) == 'r' || (**src) == 'v' ||
				(**src) == 'f'; 
        ensures \result == true;
        ensures *dst == \old(*dst + 1);
        ensures *src == \old(*src + 1);
        ensures (**dst) == unescape_space(**src);
    behavior fail:
        assumes (**src) != 'n' && (**src) != 't' &&
				(**src) != 'r' && (**src) != 'v' &&
				(**src) != 'f'; 
        ensures \result == false;
    complete behaviors;
    disjoint behaviors;
*/

static bool unescape_space(char **src, char **dst)
{
	char *p = *dst, *q = *src;

	switch (*q) {
	case 'n':
		*p = '\n';
		break;
	case 'r':
		*p = '\r';
		break;
	case 't':
		*p = '\t';
		break;
	case 'v':
		*p = '\v';
		break;
	case 'f':
		*p = '\f';
		break;
	default:
		return false;
	}
	*dst += 1;
	*src += 1;
	return true;
}

/*@ axiomatic Un_Special {
    logic char unescape_special (integer ch);
	axiom S:  unescape_special ('\"') == '\"';
	axiom SS: unescape_special ('\\') == '\\';
	axiom E:  unescape_special ('e') == '\e';
	axiom A:  unescape_special ('a') == '\a';
    }
*/

/*@
	requires \valid (src) && \valid (dst) &&
			 \valid (*src) && \valid(*dst);
	assigns (*dst), (*src);
    behavior is_special:
        assumes (**src) == '\"' || (**src) == '\\' ||
				(**src) == 'a' || (**src) == 'e';
        ensures \result == true;
        ensures *dst == \old(*dst + 1);
       ensures *src == \old(*src + 1);
        ensures (**dst) == unescape_special(**src);
    behavior fail:
         assumes (**src) != '\"' && (**src) != '\\' &&
				 (**src) != 'a' && (**src) != 'e';
         ensures \result == false;
    complete behaviors;
    disjoint behaviors;
*/

static bool unescape_special(char **src, char **dst)
{
	char *p = *dst, *q = *src;

	switch (*q) {
	case '\"':
		*p = '\"';
		break;
	case '\\':
		*p = '\\';
		break;
	case 'a':
		*p = '\a';
		break;
	case 'e':
		*p = '\e';
		break;
	default:
		return false;
	}
	*dst += 1;
	*src += 1;
	return true;
}
 
/*@ requires \valid(src + (0..size - 1));
    requires \valid(dst + (0..size - 1));
 */
 

int string_unescape(char *src, char *dst, size_t size, unsigned int flags)
{
	char *out = dst;

	while (*src && --size) {
		if (src[0] == '\\' && src[1] != '\0' && size > 1) {
			src++;
			size--;

			if (flags & UNESCAPE_SPACE &&
					unescape_space(&src, &out))
				continue;

			if (flags & UNESCAPE_OCTAL &&
					unescape_octal(&src, &out))
				continue;

			if (flags & UNESCAPE_HEX &&
					unescape_hex(&src, &out))
				continue;

			if (flags & UNESCAPE_SPECIAL &&
					unescape_special(&src, &out))
				continue;

			*out++ = '\\';
		}
		*out++ = *src++;
	}
	*out = '\0';

	return out - dst;
}
