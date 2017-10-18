/*@ predicate generic_swap {L1, L2}(char *a, char*b, integer size) =
		\forall integer i; 0 <= i < size ==>
        (\at(a[i], L1) == \at(b[i], L2)) && (\at(b[i], L1) == \at(a[i], L2));
*/
/*@ 
	requires size > 0;
    requires \typeof(a) <: \type(char *);
    requires \typeof(b) <: \type(char *);
    requires \valid((char *)a+(0..size-1));
    requires \valid((char *)b+(0..size-1));
    assigns ((char *)a)[0..size-1];
    assigns ((char *)b)[0..size-1];
    ensures generic_swap {Pre, Post}((char*)a, (char*)b, size);
 */
static void generic_swap(void *a, void *b, int size)
{
        char t;
        //@ ghost int osize = size;
        //@ ghost char *oa = (char *) a;
        //@ ghost char *ob = (char *) b;

        //@ ghost Loop:;
        /*@ loop invariant 0 <= size <= osize;
            loop invariant \typeof(a) <: \type(char *);
            loop invariant \typeof(b) <: \type(char *);
            loop invariant oa <= (char *) a < oa + osize;
            loop invariant ob <= (char *) b < ob + osize;
            loop invariant (char *)a - oa == (char *)b - ob == osize - size;
	        loop invariant 0 <= osize - size <= osize ;
            loop invariant generic_swap {Here, Pre}((char*)a, (char*)b, osize - size);
            loop invariant \forall char *p; (char *) a <= p < oa + osize ==> *p == \at(*p, Pre);
            loop invariant \forall char *p; (char *) b <= p < ob + osize ==> *p == \at(*p, Pre);
            loop assigns oa[0..osize - size];
            loop assigns ob[0..osize - size];
            loop variant size;  
*/
        do {
               t = *(char*) 
               a;
                *(char *)a++ = *(char *)b;
                *(char *)b++ = t;
        } while (--size > 0);
}
