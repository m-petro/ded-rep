// #include "escape_string_mem.h"

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst + (0..1));
	requires \base_addr(*dst) == \base_addr(end);    
    behavior is_empty:
        assumes c != 0;
        assigns \nothing;
        ensures \result == \false;
    behavior size_zero:
        assumes c == 0;
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 2);
        ensures \result == \true;
    behavior size_one:
        assumes c == 0;
        assumes *dst + 1 == end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures \result == \true;
    behavior size_two:
        assumes c == 0;
        assumes *dst + 1 < end;
        assigns *dst, **dst, *(*dst + 1);
	    ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures *(*dst - 1) == '0';
        ensures \result == \true;*/
// */

static bool escape_null(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (c)
		return false;

	if (out < end)
		*out = '\\';
	++out;
	if (out < end)
		*out = '0';
	++out;

	*dst = out;
	return true;
}

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst + (0..3));
    requires \base_addr(*dst) == \base_addr(end);
    behavior size_zero:
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 4);
        ensures \result == \true;
    behavior size_one:
        assumes *dst + 1 == end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures \result == \true;
    behavior size_two:
        assumes *dst + 2 == end;
        assigns *dst, **dst, *(*dst + 1);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == ((c / 64) % 7) + '0';
        ensures \result == \true;
    behavior size_three:
        assumes *dst + 3 == end;
        assigns *dst, **dst, *(*dst + 1), *(*dst + 2);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == ((c / 64) % 7) + '0';
        ensures *(*dst - 2) == ((c / 8) % 7) + '0';
        ensures \result == \true;
    behavior size_four:
        assumes *dst + 4 <= end;
        assigns *dst, **dst, *(*dst + 1), *(*dst + 2), 
        *(*dst + 3);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == ((c / 64) % 7) + '0';
        ensures *(*dst - 2) == ((c / 8) % 7) + '0';
        ensures *(*dst - 1) == (c % 7) + '0';
        ensures \result == \true;*/
// */

static bool escape_octal(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	/*@ assert out == *dst + 1;*/
	if (out < end)
		//CODE CHANGE BEGIN
		*out = ((c / 64) % 7) + '0';
		//*out = ((c >> 6) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	/*@ assert out == *dst + 2;*/
	if (out < end)
		//CODE CHANGE BEGIN
		*out = ((c / 8) % 7) + '0';
		//*out = ((c >> 3) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	/*@ assert out == *dst + 3;*/
	if (out < end)
		//CODE CHANGE BEGIN
		*out = (c % 7) + '0';
		//*out = ((c >> 0) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	/*@ assert out == *dst + 4;*/
// 	
	*dst = out;
	return true;
}

/*@ 
	requires \valid(end) && \valid(dst)
		&& \valid(*dst + (0..1));
    requires \base_addr(*dst) == \base_addr(end);
    behavior size_zero:
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 1);
        ensures \result == \true;
    behavior size_one:
        assumes *dst < end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 1);
        ensures \old(**dst) == (char)c;
        ensures \result == \true;
    complete behaviors;
    disjoint behaviors;*/
// */

static bool escape_passthrough(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
	// code changed
		/*@ assert out == *dst;*/
		*out = (char)c;
	*dst = out + 1;
	return true;
}


/*@ axiomatic Es_Space {
    	logic char escape_space (integer ch);
		axiom N: escape_space ('\n') == 'n';
		axiom R: escape_space ('\r') == 'r';
		axiom T: escape_space ('\t') == 't';	
		axiom V: escape_space ('\v') == 'v';
		axiom F: escape_space ('\f') == 'f';
    }*/
// */

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst + (0..1));
    requires \base_addr(*dst) == \base_addr(end);
    behavior is_empty:
        assumes c != '\n' && c != '\t' &&
				c != '\r' && c != '\v' &&
				c != '\f'; 
        assigns \nothing;
        ensures \result == \false;
    behavior size_zero:
		assumes c == '\n' || c == '\t' ||
				c == '\r' || c == '\v' ||
				c == '\f'; 
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 2);
        ensures \result == \true;
    behavior size_one:
        assumes c == '\n' || c == '\t' ||
				c == '\r' || c == '\v' ||
				c == '\f'; 
        assumes *dst + 1 == end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures \result == \true;
    behavior size_two:
        assumes c == '\n' || c == '\t' ||
				c == '\r' || c == '\v' ||
				c == '\f'; 
        assumes *dst + 1 < end;
        assigns *dst, **dst, *(*dst + 1);
	    ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures *(*dst - 1) == escape_space (c);
        ensures \result == \true;*/
// */

static bool escape_space(unsigned char c, char **dst, char *end)
{
	char *out = *dst;
	unsigned char to;

	switch (c) {
	case '\n':
		to = 'n';
		break;
	case '\r':
		to = 'r';
		break;
	case '\t':
		to = 't';
		break;
	case '\v':
		to = 'v';
		break;
	case '\f':
		to = 'f';
		break;
	default:
		return false;
	}

	if (out < end)
		*out = '\\';
	++out;
	if (out < end)
		*out = to;
	++out;

	*dst = out;
	return true;
}

/*@ axiomatic Es_Special {
    	logic char escape_special (integer ch);
		axiom Sl:  escape_special ('\\') == '\\';
		axiom A:   escape_special ('\a') == 'a';
		axiom E:   escape_special ('\e') == 'e';	
    }*/
// */

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst + (0..1));
    requires \base_addr(*dst) == \base_addr(end);
    behavior is_empty:
        assumes c != '\\' && c != '\a' &&
				c != '\e'; 
        assigns \nothing;
        ensures \result == \false;
    behavior size_zero:
		assumes c == '\\' || c == '\a' ||
				c == '\e'; 
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 2);
        ensures \result == \true;
    behavior size_one:
        assumes c == '\\' || c == '\a' ||
				c == '\e'; 
        assumes *dst + 1 == end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures \result == \true;
    behavior size_two:
        assumes c == '\\' || c == '\a' ||
				c == '\e'; 
        assumes *dst + 1 < end;
        assigns *dst, **dst, *(*dst + 1);
	    ensures *dst == \old(*dst + 2);
        ensures *(*dst - 2) == '\\';
        ensures *(*dst - 1) == escape_special (c);
        ensures \result == \true;*/
// */

static bool escape_special(unsigned char c, char **dst, char *end)
{
	char *out = *dst;
	unsigned char to;

	switch (c) {
	case '\\':
		to = '\\';
		break;
	case '\a':
		to = 'a';
		break;
	case '\e':
		to = 'e';
		break;
	default:
		return false;
	}

	if (out < end)
		*out = '\\';
	++out;
	if (out < end)
		*out = to;
	++out;

	*dst = out;
	return true;
}

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst + (0..3));
    requires \base_addr(*dst) == \base_addr(end);
    behavior size_zero:
        assumes *dst >= end;
        assigns *dst;
        ensures *dst == \old(*dst + 4);
        ensures \result == \true;
    behavior size_one:
        assumes *dst + 1 == end;
        assigns *dst, **dst;
        ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures \result == \true;
    behavior size_two:
        assumes *dst + 2 == end;
        assigns *dst, **dst, *(*dst + 1);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == 'x';
        ensures \result == \true;
    behavior size_three:
        assumes *dst + 3 == end;
        assigns *dst, **dst, *(*dst + 1), *(*dst + 2);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == 'x';
        ensures *(*dst - 2) == hex_asc[((c) % 240) / 16];
        ensures \result == \true;
    behavior size_four:
        assumes *dst + 4 <= end;
        assigns *dst, **dst, *(*dst + 1), *(*dst + 2), *(*dst + 3);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == 'x';
        ensures *(*dst - 2) == hex_asc[((c) % 240) / 16];
        ensures *(*dst - 1) == hex_asc[((c) % 15)];
        ensures \result == \true;*/
// */


static bool escape_hex(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	/*@ assert out == *dst + 1;*/
	if (out < end)
		*out = 'x';
	++out;
	/*@ assert out == *dst + 2;*/
	if (out < end)
		*out = hex_asc[((c) % 240) / 16];
	++out;
	/*@ assert out == *dst + 3;*/
	if (out < end)
		*out = hex_asc[((c) % 15)];
	++out;
	/*@ assert out == *dst + 4;*/

	*dst = out;
	return true;
}
/* @
	requires \valid(src + (0..size - 1));
    requires \valid(dst + (0..size - 1));
	behavior empty:
	assumes 
		(\forall integer i; 0 <= i < size ==> src[i] != '//') 
		|| (((flags & (unsigned int)ESCAPE_SPACE) == 0) &&
			((flags & (unsigned int)ESCAPE_OCTAL) == 0) &&
			((flags & (unsigned int)ESCAPE_HEX) == 0)   &&
			((flags & (unsigned int)ESCAPE_SPECIAL) == 0)); 							 
	assigns dst[0..size - 1];
	ensures \result == (size - 1);
	ensures 
		\forall integer i; 0 <= i < size ==> dst[i] == src[i];
*/




int string_escape_mem(const char *src, size_t isz, char *dst, size_t osz,
		      unsigned int flags, const char *only)
{
	char *p = dst;
	char *end = p + osz;
	bool is_dict = only && *only;

	while (isz--) {
		unsigned char c = *src++;

		/*
		 * Apply rules in the following sequence:
		 *	- the character is printable, when @flags has
		 *	  %ESCAPE_NP bit set
		 *	- the @only string is supplied and does not contain a
		 *	  character under question
		 *	- the character doesn't fall into a class of symbols
		 *	  defined by given @flags
		 * In these cases we just pass through a character to the
		 * output buffer.
		 */

		if ((flags & 0x10 && (((_ctype[(int)(unsigned char)(c)])&(0x10|0x01|0x02|0x04|0x80)) != 0)) ||
		    (is_dict && !strchr(only, c))) {
			/* do nothing */
		} else {
			if (flags & 0x01 && escape_space(c, &p, end))
				continue;

			if (flags & 0x02 && escape_special(c, &p, end))
				continue;

			if (flags & 0x04 && escape_null(c, &p, end))
				continue;

			/* ESCAPE_OCTAL and ESCAPE_HEX always go last */
			if (flags & 0x08 && escape_octal(c, &p, end))
				continue;

			if (flags & 0x20 && escape_hex(c, &p, end))
				continue;
		}

		escape_passthrough(c, &p, end);
	}

	return p - dst;
}
