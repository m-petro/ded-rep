#include "string_escape_mem.h"

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

static bool escape_octal(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	if (out < end)
		*out = ((c >> 6) & 0x07) + '0';
	++out;
	if (out < end)
		*out = ((c >> 3) & 0x07) + '0';
	++out;
	if (out < end)
		*out = ((c >> 0) & 0x07) + '0';
	++out;

	*dst = out;
	return true;
}

static bool escape_passthrough(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = c;
	*dst = out + 1;
	return true;
}

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

static bool escape_hex(unsigned char c, char **dst, char *end)
{
	char *out = *dst;

	if (out < end)
		*out = '\\';
	++out;
	if (out < end)
		*out = 'x';
	++out;
	if (out < end)
		*out = hex_asc_hi(c);
	++out;
	if (out < end)
		*out = hex_asc_lo(c);
	++out;

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
