
// #include <linux/export.h>
// #include <linux/bsearch.h>
#include <string.h>

/* 
	predicate sorted(char *a, int (*cmp)(char*, char*), integer n)
									= \forall integer i, j; 0 <= i < j < n  ==> cmp(a[i], a[j]) >= 0;
*/

int cmp_1(const void *key, const void *elt)
{
   return 0;
}

/*@
   requires cmp == cmp_1;
	requires \typeof(key) <: \type(char *);
	requires \typeof(base) <: \type(char *);
	requires \valid((char *)base +(0..(num - 1) * size));
	requires \valid((char *)key);
	requires \valid((char *)cmp);
	//requires sorted((char *)base, cmp, num);
	assigns  \nothing;

	//behavior exist:
      //assumes \exists integer i; 0 <= i < num  ==> cmp(((char*)base)[i], key) == 0;
		//ensures cmp(\result, key) == 0;

	//behavior not_exist:
		//assumes !\exists integer i; 0 <= i < num ==> cmp(((char*)base)[i], key) == 0;
		//ensures \result == NULL;
*/

void *bsearch(const void *key, const void *base, size_t num, size_t size,
	      int (*cmp)(const void *key, const void *elt))
{
	const char *pivot;
	int result;

	/*
		loop invariant base <= pivot <= base + num;
		loop variant num;
	 */

	while (num > 0) {
		pivot = base + (num / 2) * size;
		// src: pivot = base + (num >> 1) * size;
		result = cmp(key, pivot);

		if (result == 0)
			return (void *)pivot;

		if (result > 0) {
			base = pivot + size;
			num--;
		}
		num = num / 2;
		// src: num >>= 1;
	}
	return NULL;
}
// EXPORT_SYMBOL(bsearch);
