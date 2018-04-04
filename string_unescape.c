#include "string_unescape.h"


/*@
	axiomatic len_of_hex 
	{
    	logic size_t len_of_hex{L}(char *x);
		axiom NH: \forall char *x; *x != 'x' ==> len_of_hex(x) ==  0;
		axiom L0: \forall char *x; *x == 'x' &&  !isxdigit(*(x + 1)) ==> len_of_hex(x) ==  1;
		axiom L1: \forall char *x; *x == 'x' &&  isxdigit(*(x + 1)) && !isxdigit(*(x + 2))
																		 ==> len_of_hex(x) ==  2;
		axiom L2: \forall char *x; *x == 'x' &&  isxdigit(*(x + 1)) && isxdigit(*(x + 2))
																	     ==> len_of_hex(x) ==  3;
	}

*/ 

/*@ 
	requires \valid(src) && \valid(*src);
    requires \valid(dst) && \valid(*dst);
    requires \valid(*src + (0..(len_of_hex(*src))));
    behavior not_hex:
        assumes len_of_hex(*src) == 0 || len_of_hex(*src) == 1;
   		assigns *src;
   		ensures *src == \old(*src + 1 + len_of_hex(*\old(src)));
		ensures \result == \false;
    behavior valid_hex:
        assumes len_of_hex(*src) == 2 ||  len_of_hex(*src) == 3;
        assigns **dst, *dst, *src;
		ensures len_of_hex(*src) == 2 ==> *(\old(*dst)) == hex_to_bin(*(*\old(src) + 1));
		ensures len_of_hex(*src) == 3 ==> *(\old(*dst)) == hex_to_bin(*(*\old(src) + 1)) * 16
																  + hex_to_bin(*(*\old(src) + 2));
        ensures *src == \old(*src + len_of_hex(*\old(src)));
		ensures *dst == \old(*dst + 1);
		ensures \result == \true;

*/
 
static bool unescape_hex(char **src, char **dst)
{
	char *p = *dst, *q = *src;
	int digit;
	u8 num;

	if (*q++ != 'x')
		return false;
	//@ assert q == *src + 1;	
	//CODE CHANGE BEGIN
	digit = hex_to_bin(*q++); 
	//@ assert q == *src + 2;
	if (digit < 0)
		return false;
	num = digit;
	//CODE CHANGE END
	digit = hex_to_bin(*q);
	if (digit >= 0) {
		q++;
		//@ assert q == *src + 3;
		//CODE CHANGE BEGIN
		//@ assert 0 <= digit <= 15;
		//@ assert 0 <= num <= 15;
		num = num * 16;
		//@ assert 0 <= num <= 15 * 16;
		num =+ digit;
		//CODE CHANGE END
	}
	*p = num;
	*dst += 1;
	*src = q;
	return true;
}

/*@
	axiomatic len_of_octal 
	{
    	logic size_t len_of_octal{L}(char *x);
		axiom NO: \forall char *x; !isodigit(*x) ==> len_of_octal(x) == 0;
		axiom O0: \forall char *x; isodigit(*x) && !isodigit(*(x + 1)) ==> len_of_octal(x) == 1;
		axiom O1: \forall char *x; isodigit(*x) && isodigit(*(x + 1)) && !isodigit(*(x + 2))
																		 ==> len_of_octal(x) == 2;
		axiom O2: \forall char *x; isodigit(*x) && isodigit(*(x + 1)) && isodigit(*(x + 2))
																	     ==> len_of_octal(x) == 3;
	}

*/ 

/*@ 
	requires \valid(src) && \valid(*src);
    requires \valid(dst) && \valid(*dst);
    requires \valid(*src + (0..len_of_octal(*src)));
    behavior not_hex:
    	assumes len_of_octal(*src) == 0;
   		assigns \nothing;
    	ensures \result == \false;
    behavior valid_hex:
    	assumes len_of_hex(*src) == 2 ||  len_of_hex(*src) == 3;
    	assigns **dst, *dst, *src;
		ensures len_of_octal(*src) == 2 ==> *(\old(*dst)) == (**\old(src)) + 8 * (*(\old(*src + 1)));
		ensures len_of_octal(*src) == 3 ==> *(\old(*dst)) == (**\old(src)) + 8 * (*(\old(*src + 1))) + 64 * (*(\old(*src + 2)));
    	ensures *src == \old(*src + len_of_octal(*\old(src)));
		ensures *dst == \old(*dst + 1);
		ensures \result == \true;
*/

static bool unescape_octal(char **src, char **dst)
{
	char *p = *dst, *q = *src;
	u8 num;

	if (isodigit(*q) == 0)
		return false;
	//CODE CHANGE BEGIN
	num = (*q++) % 8;
	//@ assert q == *src + 1;
	//@ assert 0 <= num <= 6;
	//CODE CHANGE END

	/*@ 
	 loop invariant *src < q <= 3 + *src;
	 loop invariant num < 32 * 8;
	 loop variant  3 - (q - *src); 
	*/
	while (num < 32 && isodigit(*q) && (q - *src < 3)) {
		//CODE CHANGE BEGIN
		num *= 8; 	
		num += (*q++) % 8; 
		//CODE CHANGE END
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

//@ predicate is_space(integer c) = (c == 'n' || c == 'r' || c == 't'  || c == 'v' || c == 'f'); 

/*@
	requires \valid (src) && \valid (dst) &&
			 \valid (*src) && \valid(*dst);
	assigns (**dst), *src, *dst;
    behavior is_space:
        assumes is_space(**src);
        ensures \result == true;
        ensures *dst == \old(*dst + 1);
        ensures *src == \old(*src + 1);
        ensures (*(*dst - 1)) == unescape_space(*(*src - 1));
    behavior fail:
        assumes !is_space(**src);
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
    logic char unescape_special (char ch);
	axiom S:  unescape_special ('\"') == '\"';
	axiom SS: unescape_special ('\\') == '\\';
	axiom E:  unescape_special ('e') == '\e';
	axiom A:  unescape_special ('a') == '\a';
    }
*/

//@ predicate is_special(integer c) = (c == '\"' || c == '\\' || c == 'e'  || c == 'a'); 

/*@
	requires \valid (src) && \valid (dst) &&  								
			 \valid (*src) && \valid(*dst);
	assigns (**dst), *dst, *src;
    behavior is_special:
        assumes is_special(**src);
        ensures \result == true;
        ensures *dst == \old(*dst + 1);
        ensures *src == \old(*src + 1);
        ensures (*(*dst - 1)) == unescape_special(*(*src - 1));
														
    behavior fail:
         assumes !is_special(**src);
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
	behavior empty:
	assumes 
		(\forall integer i; 0 <= i < size ==> src[i] != '//') 
		|| (((flags & (unsigned int)UNESCAPE_SPACE) == 0) &&
			((flags & (unsigned int)UNESCAPE_OCTAL) == 0) &&
			((flags & (unsigned int)UNESCAPE_HEX) == 0)   &&
			((flags & (unsigned int)UNESCAPE_SPECIAL) == 0)); 							 
	assigns dst[0..size - 1];
	ensures \result == (size - 1);
	
	ensures \true;
	//	ensures 
	//	\forall integer i; 0 <= i < size ==> dst[i] == src[i];

	//behavior is_octal:
	//assumes 
	//	(flags & (unsigned int)UNESCAPE_SPACE) != 0;
	//assigns dst[0..size - 1];
	
	//ensures 
	//	\forall integer i; 0 <= i < size && src[i] is_octal ==> dst[i] == unescape_space(src[i]);
    //ensures 
	//behavior is_special:
	//assumes
	//	(flags & (unsigned int)UNESCAPE_SPECIAL) != 0;
	//assigns dst[1..size - 1];
		
	//behavior is_space:
	//assumes
	//	(flags & (unsigned int)UNESCAPE_SPACE) != 0;
	//behavior is_hex:
	//assumes
	//	(flags & (unsigned int)UNESCAPE_HEX) != 0; 
		
	
	
 */
 

int string_unescape(char *src, char *dst, size_t size, unsigned int flags)
{
	//@ ghost char *osrc = (char *) src;
	//@ ghost int osize = size;
	char *out = dst;
		/*@
			loop invariant  osrc <= src < osrc + osize;
			loop invariant 0 <= size <= osize;
			loop variant size; 
		*/
	while (*src && --size) {
		if (src[0] == '\\' && src[1] != '\0' && size > 1) {
			src++;
			size--;
	/*
			if (flags & UNESCAPE_SPACE &&
					unescape_space(&src, &out))
				continue;

			if (flags & UNESCAPE_OCTAL &&
					unescape_octal(&src, &out))
				continue;

			if (flags & UNESCAPE_HEX &&
					unescape_hex(&src, &out))
				continue;
	*/

			// comment it and verify by parts
			// copy str_len.h from str_len


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

