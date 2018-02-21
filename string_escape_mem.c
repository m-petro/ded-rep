#include "string_escape_mem.h"

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst) && \valid(*dst + 1);
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
        ensures \result == \true;
*/

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
	requires \valid(end);
	requires \valid(dst) && \valid(*dst + (0..3));
    
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
        ensures \result == \true;
*/

static bool escape_octal(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	//@ assert out == *dst + 1;
	if (out < end)
		//CODE CHANGE BEGIN
		*out = ((c / 64) % 7) + '0';
		//*out = ((c >> 6) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 2;
	if (out < end)
		//CODE CHANGE BEGIN
		*out = ((c / 8) % 7) + '0';
		//*out = ((c >> 3) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 3;
	if (out < end)
		//CODE CHANGE BEGIN
		*out = (c % 7) + '0';
		//*out = ((c >> 0) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 4;
	
	*dst = out;
	return true;
}

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst) && \valid(*dst + 1);
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
        ensures *(*dst - 1) == c;
        ensures \result == \true;
*/

static bool escape_passthrough(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = (char)/*@%*/c; // CODE CHANGE
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
    }
*/

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst) && \valid(*dst + 1);
    
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
        ensures \result == \true;
*/

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
    }
*/

/*@ 
	requires \valid(end) && \valid(dst)
		 && \valid(*dst) && \valid(*dst + 1);
    
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
        ensures \result == \true;
*/

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
		 && \valid(*dst) && \valid(*dst + 1)
		 && \valid(*dst + 2) && \valid(*dst + 3);
    
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
        ensures *(*dst - 2) == hex_asc_hi(c);
        ensures \result == \true;
    behavior size_four:
        assumes *dst + 4 <= end;
        assigns *dst, **dst, *(*dst + 1), *(*dst + 2), *(*dst + 3);
	    ensures *dst == \old(*dst + 4);
        ensures *(*dst - 4) == '\\';
        ensures *(*dst - 3) == 'x';
        ensures *(*dst - 2) == hex_asc_hi(c);
        ensures *(*dst - 1) == hex_asc_lo(c);
        ensures \result == \true;
*/


static bool escape_hex(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	//@ assert out == *dst + 1;
	if (out < end)
		*out = 'x';
	++out;
	//@ assert out == *dst + 2;
	if (out < end)
		*out = hex_asc_hi(c);
	++out;
	//@ assert out == *dst + 3;
	if (out < end)
		*out = hex_asc_lo(c);
	++out;
	//@ assert out == *dst + 4;

	*dst = out;
	return true;
}

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

		if ((flags & ESCAPE_NP && isprint(c)) ||
		    (is_dict && !strchr(only, c))) {
			/* do nothing */
		} else {
			if (flags & ESCAPE_SPACE && escape_space(c, &p, end))
				continue;

			if (flags & ESCAPE_SPECIAL && escape_special(c, &p, end))
				continue;

			if (flags & ESCAPE_NULL && escape_null(c, &p, end))
				continue;

			/* ESCAPE_OCTAL and ESCAPE_HEX always go last */
			if (flags & ESCAPE_OCTAL && escape_octal(c, &p, end))
				continue;

			if (flags & ESCAPE_HEX && escape_hex(c, &p, end))
				continue;
		}

		escape_passthrough(c, &p, end);
	}

	return p - dst;
}
