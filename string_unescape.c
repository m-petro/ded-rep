#include "string_unescape.h"


//Нужна простая проверочная функция для тестирования работы requires под assumes
/*@ requires \true;
    requires \valid(a);
    behavior len_2:
    	assumes len == 2;
	requires \valid(a + (0..2));
    behavior len_3:
    	assumes len == 3;
	requires \valid(a + (0..3));
*/
int test_requires(int *a, unsigned int len) {
	*a++ = 0;
	if (len <= 1)
		*a++ = 0;
	if (len <= 2)
		*a = 0;
}

/*@ requires \valid(src) && \valid(*src);
    requires \valid(dst) && \valid(*dst);
    requires (**src == 'x' && !isxdigit(*(*src + 1))) ==> \valid(*src + 1);
    requires ...

    behavior not_x:
        assumes **src != 'x';
        assigns *src;
        ensures *src == \old(*src + 1);
        ensures \result == \false;
       
    behavior not_hex:
        assumes **src == 'x' && !isxdigit(*(*src + 1));
        requires \valid(*src + 1);
        assigns *src;
        ensures *src == \old(*src + 2);
        ensures \result == \false;
    
    behavior one_digit:
        assumes **src == 'x';
        assumes isxdigit(*(*src + 1));
        assumes !isxdigit(*(*src + 2));
        requires \valid(*src + 1);
        requires \valid(*src + 2);
        assigns **dst, *dst, *src;
        ensures *dst == \old(*dst + 1);
        ensures *src == \old(*src + 2);
        ensures *(\old(*dst)) == hex_to_bin(*(*\old(src) + 1));
        ensures \result == \true;
   behavior two_digits:
       assumes **src == 'x';
       assumes isxdigit(*(*src + 1));
       assumes isxdigit(*(*src + 2));
       requires \valid(*src + (0..2));
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
	//CODE CHANGE BEGIN
	digit = hex_to_bin(*q++); 
	//@ for not_hex: assert digit == -1;
	//@ for one_digit: assert 0 <= digit <= 15;
	//@ for two_digits: assert 0 <= digit <= 15; 
	//@ assert q == *src + 2;
	if (digit < 0)
		return false;
	//@ assert 0 <= digit <= 15;
	num = digit;
	//@ assert 0 <= num <= 15;
	//CODE CHANGE END
	digit = hex_to_bin(*q);
	//@ for one_digit: assert digit == -1; 
	//@ for two_digits: assert 0 <= digit <= 15; 
	if (digit >= 0) {
		q++;
		//@ assert q == *src + 3;
		//CODE CHANGE BEGIN
		//@ assert 0 <= num <= 15;
		num *= 16;
		//@ assert 0 <= num <= 240;
		//@ assert 0 <= digit <= 15;
		num += digit;
		//@ assert 0 <= num <= 255;
		//CODE CHANGE END
	}
	*p = num;
	//@ assert p == *dst;
	*dst += 1;
	//@ assert p == *dst + 1;
	//@ for one_digit: assert q == (*src + 2); 
	//@ for two_digits: assert q == (*src + 3);
	*src = q;
	return true;
}

/*@ logic u8 octal_to_decimal(char *o, integer len) =
	(len == 0) ? 0 :
	(len == 1) ? *o % 7
	либо через аксиомы,  где явно во второй аргуемнт вставляете константу
	axiom o1:
		\forall char *o; \valid(o) ==> octal_to_decimal(o, 1) == *o % 7;
*/

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
       requires \valid(*src + 1);
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
	//CODE CHANGE BEGIN
	num = (*q++) % 7;
	//@ assert q == *src + 1;
	//@ assert 0 <= num <= 6;
	//CODE CHANGE END
	
	//ghost char *q_before_cycle = q;
	
	/*@
	 loop invariant *src < q <= *src + 3;
	 loop invariant \forall char *x; q_before_cycle <= x < q ==> isodigit(x);
	 loop invariant num == octal_to_decimal(src, q - *src);
	 loop variant 3 - (q - *src); 
	*/
	while (num < 32 && isodigit(*q) && (q - *src < 3)) {
		//CODE CHANGE BEGIN
		num *= 8; 
		num += (*q++) % 7; 
		//CODE CHANGE END
	}
	if (isodigit(*q)) {
		num *= 8;
		num += (*q++) % 7;
	}
	
	if (num < 32 && isodigit(*q)) {
		num *= 8;
		num += (*q++) % 7;
	}
	
	*p = num;
	*dst += 1;
	*src = q;
	return true;
}

void test_code_changes(void) {
	for(u8 i = 0; i <= U8INT_MAX; ++i) {
		if (i & 7 != i % 7) {
			printf("INEQUALITY %d %d %d\n", i, i & 7, i % 7);
		}
	}
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
        ensures (*(*dst - 1)) == unescape_space(*(*src - 1));
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
    logic char unescape_special (char ch);
	axiom S:  unescape_special ('\"') == '\"';
	axiom SS: unescape_special ('\\') == '\\';
	axiom E:  unescape_special ('e') == '\e';
	axiom A:  unescape_special ('a') == '\a';
    }
*/

/*@ predicate is_special(integer c) = (c == '\"' || c == '\\' 
 				|| c == 'e'  || c == 'a'); */

/*@
	requires \valid (src) && \valid (dst) &&  				// переписать на предикатах						
			 \valid (*src) && \valid(*dst);
	assigns (**dst), *dst, *src;
    behavior is_special:
        assumes (**src) == '\"' || (**src) == '\\' ||
				(**src) == 'e'  || (**src) == 'a';
        ensures \result == true;
        ensures *dst == \old(*dst + 1);
        ensures *src == \old(*src + 1);
        ensures (*(*dst - 1)) == unescape_special(*(*src - 1));
														
    behavior fail:
         assumes (**src) != '\"' && (**src) != '\\' &&
				 (**src) != 'e'  && (**src) != 'a';   // '\e' !!
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
	ensures 
		\forall integer i; 0 <= i < size ==> dst[i] == src[i];

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
			/* попробуйте потребовать что флаги не выставлены и доказать без них
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
			*/

			*out++ = '\\';
		}
		*out++ = *src++;
	}
	*out = '\0';

	return out - dst;
}
