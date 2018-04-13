#include "escape_string_mem.h"

/*@

predicate null(size_t size, char* src, unsigned char c) =
		\forall size_t i; 0 < i <= size && i < 3 ==> src[i-1] == null_get_value(i, c);
	
	axiomatic null_get_value {
    logic char null_get_value{L} (size_t i, unsigned char c);
		axiom N1:  \forall unsigned char c; null_get_value (1, c) == '\\';
		axiom N2:  \forall unsigned char c; null_get_value (2, c) == '0';
	}	
*/

/*@ 
	requires \valid(end) && \valid(dst);
	requires \valid(*dst + (0..1));
	requires \base_addr(*dst) == \base_addr(end);
	behavior is_empty:
		assumes c == 0;
		assigns \nothing;
		ensures \result == \false;
	behavior not_empty:
		assumes c != 0;
		assigns *dst, *dst[0..(end - *dst)];
		ensures *dst == \old(*dst + 2);
		ensures null((size_t)(end - *dst), \old(*dst),  c);
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


/*@ predicate octal(size_t size, char* src, unsigned char c) =
			\forall size_t i; 0 <= i <= size && i < 4 ==> src[i] == octal_get_value(i, c);

	axiomatic octal_get_value {
	logic char octal_get_value{L} (size_t i, unsigned char c);
		axiom O1:  \forall unsigned char c; octal_get_value (0, c) == '\\';
		axiom O2:  \forall unsigned char c; octal_get_value (1, c) == ((c / 64) % 7) + '0';
		axiom O3:  \forall unsigned char c; octal_get_value (2, c) == ((c / 8) % 7) + '0';
		axiom O4:  \forall unsigned char c; octal_get_value (3, c) == (c % 7) + '0';	
	}
*/

/*@ 
	requires \valid(end) && \valid(dst);
	requires \valid(*dst + (0..(end - *dst)));
	requires \base_addr(*dst) == \base_addr(end);
	assigns *dst, *dst[0..(end - *dst)];
	behavior not_empty:
		ensures *dst == \old(*dst + 4);
		ensures octal((size_t)(end - *dst), \old(*dst), c);
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
		*out = ((c / 64) % 8) + '0';
		//*out = ((c >> 6) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 2;
	if (out < end)
		//CODE CHANGE BEGIN
		*out = ((c / 8) % 8) + '0';
		//*out = ((c >> 3) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 3;
	if (out < end)
		//CODE CHANGE BEGIN
		*out = (c % 8) + '0';
		//*out = ((c >> 0) & 0x07) + '0';
		//CODE CHANGE END
	++out;
	//@ assert out == *dst + 4;	
	*dst = out;
	return true;
}

/*@ 
	requires \valid(end) && \valid(dst);
	requires \valid(*dst + (0..1));
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
		ensures *\old(*dst) == (char %)c;
		ensures \result == \true;
	complete behaviors;
	disjoint behaviors;
*/

static bool escape_passthrough(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		// code changed
		*out = (char)/*@%*/c;
	*dst = out + 1;
	return true;
}
/*@

	predicate space(size_t size, char* src, unsigned char c) =
			\forall size_t i; 0 < i <= size && i < 3 ==> src[i-1] == space_get_value(i, c);

	axiomatic space_get_value {
    logic char space_get_value{L} (size_t i, unsigned char c);
		axiom Sp1:  \forall unsigned char c; space_get_value (1, c) == '\\';
		axiom Sp2:  \forall unsigned char c; space_get_value (2, c) == escape_special(c);
	}
	axiomatic Es_Space {
	logic char escape_space (integer ch);
		axiom N: escape_space ('\n') == 'n';
		axiom R: escape_space ('\r') == 'r';
		axiom T: escape_space ('\t') == 't';	
		axiom V: escape_space ('\v') == 'v';
		axiom F: escape_space ('\f') == 'f';
	}
*/
/*@ 
	requires \valid(end) && \valid(dst);
	requires \valid(*dst + (0..1));
	requires \base_addr(*dst) == \base_addr(end);
	behavior is_empty:
		assumes c != '\n' && c != '\t' &&
				c != '\r' && c != '\v' &&
				c != '\f'; 
		assigns \nothing;
		ensures \result == \false;
	behavior not_empty:
		assumes c == '\n' || c == '\t' ||
				c == '\r' || c == '\v' ||
				c == '\f'; 
		assigns *dst, *dst[0..(end - *dst)];
		ensures *dst == \old(*dst + 2);
		ensures special ((size_t)(end - *dst), \old(*dst),  c);
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

/*@ predicate special(size_t size, char* src, unsigned char c) =
			\forall size_t i; 0 < i <= size && i < 3 ==> src[i-1] == special_get_value(i, c);
	axiomatic special_get_value {
	logic char special_get_value{L} (size_t i, unsigned char c);
		axiom S1:  \forall unsigned char c; special_get_value (1, c) == '\\';
		axiom S2:  \forall unsigned char c; special_get_value (2, c) == escape_special(c);
	}
	axiomatic Es_Special {
	logic char escape_special (integer c);
		axiom Sl: escape_special ('\\') == '\\';
		axiom A:  escape_special ('\a') == 'a';
		axiom E:  escape_special ('\e') == 'e';	
	}
*/

/*@ 
	requires \valid(end) && \valid(dst);
	requires \valid(*dst + (0..(end - *dst)));
	requires \base_addr(*dst) == \base_addr(end);
	behavior is_empty:
		assumes c != '\\' && c != '\a' &&
				c != '\e'; 
		assigns \nothing;
		ensures \result == \false;
	behavior not_empty:
		assumes c == '\\' || c == '\a' ||
				c == '\e'; 
		assigns *dst, *dst[0..(end - *dst)];
		ensures *dst == \old(*dst + 2);
		ensures special ((size_t)(end - *dst), \old(*dst),  c);
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

/*@ predicate hex(size_t size, char* src, unsigned char c) =
			\forall size_t i; 0 <= i <= size && i < 4 ==> src[i] == hex_get_value(i, c);
	axiomatic hex_get_value {
	logic char hex_get_value{L} (size_t i, unsigned char c);
		axiom H1: \forall unsigned char c; hex_get_value (0, c) == '\\';
		axiom H2: \forall unsigned char c; hex_get_value (1, c) == 'x';
		axiom H3: \forall unsigned char c; hex_get_value (2, c) == hex_asc_hi(c);
		axiom H4: \forall unsigned char c; hex_get_value (3, c) == hex_asc_lo(c);	
	}
*/

/*@ 
	requires \valid(end);
	requires \valid(*dst + (0..(end - *dst)));
	requires \base_addr(*dst) == \base_addr(end);
	assigns *dst, *dst[0..(end - *dst)];
	ensures *dst == \old(*dst + 4);
	ensures \result == \true;
	ensures hex((size_t)(end - *dst), \old(*dst), c);
*/

static bool escape_hex(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	//@ assert (end - *dst) == 1;
	if (out < end)
		*out = 'x';
	++out;
	//@ assert (end - *dst) == 2;
	if (out < end)
		*out = hex_asc_hi(c);
	++out;
	//@ assert (end - *dst) == 3;
	if (out < end)
		*out = hex_asc_lo(c);
	++out;
	//@ assert (end - *dst) == 4;
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
