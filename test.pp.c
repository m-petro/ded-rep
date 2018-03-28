
/*@ requires \true;
    requires \valid(a);
    behavior len_1:
    	assumes len == 1;
		requires \valid(a + 1);
    behavior len_2:
    	assumes len == 2;
		requires \valid(a + 2);*/
// */
//  
int test_requires(int *a, unsigned int len) {
	*a++ = 0;
	if (len == 1)
		*a++ = 0;
	if (len == 2)
		*a = 0;
	return 0;
}
