//#include <linux/module.h>
//#include <linux/bitops.h>
//#include <asm/types.h>

#include <stdint.h>
#include <math.h> 

int xor_5(unsigned int src, size_t st){
	// 0x55.. = 0101.0101..b
	unsigned int tmp = src;
	for (float i = st; i > 0; i = i - 2.0f){

		if (powf(2.0f, i - 1.0f) <= tmp) {
			src -= powf(2.0f, i - 1.0f);
			tmp -= powf(2.0f, i - 1.0f);
		}
		if (powf(2.0f, i - 2.0f) <= tmp) tmp -= powf(2.0f, i - 2.0f);
	}
	return src;
}

int xor_3(unsigned int src, size_t st){
	// 0x33.. = 0011.0011..b
	unsigned int tmp = src;
	for (float i = st; i > 0; i = i - 4.0f){

		if (powf(2.0f, i - 1.0f) <= tmp) {
			src -= powf(2.0f, i - 1.0f);
			tmp -= powf(2.0f, i - 1.0f);
		}
		if (powf(2.0f, i - 2.0f) <= tmp) {
			src -= powf(2.0f, i - 2.0f);
			tmp -= powf(2.0f, i - 2.0f);
		}
		if (powf(2.0f, i - 3.0f) <= tmp) tmp -= powf(2.0f, i - 3.0f);
		if (powf(2.0f, i - 4.0f) <= tmp) tmp -= powf(2.0f, i - 4.0f);
	}
	return src;
}

int xor_F(unsigned int src, size_t st){
	// 0x0F.. = 0000.1111..b
	unsigned int tmp = src;
	int is_odd = 1;
	for (float i = st; i > 0; i = i - 4.0f){
		if ((powf(2.0f, i - 1.0f) <= tmp) && is_odd) {
			src -= powf(2.0f, i - 1.0f);
			tmp -= powf(2.0f, i - 1.0f);
		}
		else 
			tmp -= powf(2.0f, i - 1.0f); 
		if ((powf(2.0f, i - 2.0f) <= tmp) && is_odd) {
			src -= powf(2.0f, i - 2.0f);
			tmp -= powf(2.0f, i - 2.0f);
		}	
		else
			tmp -= powf(2.0f, i - 2.0f);
		if ((powf(2.0f, i - 3.0f) <= tmp) && is_odd) {
			src -= powf(2.0f, i - 3.0f);
			tmp -= powf(2.0f, i - 3.0f);
		}
		else 
			tmp -= powf(2.0f, i - 2.0f);
		if ((powf(2.0f, i - 4.0f) <= tmp) && is_odd){
			src -= powf(2.0f, i - 4.0f);
			tmp -= powf(2.0f, i - 4.0f);
		}
		else
			tmp -= powf(2.0f, i - 4.0f);
		if (is_odd) is_odd = 0;
		else is_odd = 1; 
	}
	return src;
}

/**
 * hweightN - returns the hamming weight of a N-bit word
 * @x: the word to weigh
 *
 * The Hamming Weight of a number is the total number of bits set in it.
 */

typedef uint64_t __u64;



unsigned int hweight32(unsigned int w)
{
	// CHANGED CODE START
	unsigned int res = w - xor_5(w / 2, 32) ;
	// src: unsigned int res = w - ((w >> 1) & 0x55555555);
	res = (res % 858993460) + xor_3(res / 4, 32);
	// src: res = (res & 0x33333333) + ((res >> 2) & 0x33333333);
	res = xor_F(res + (res / 16), 32);
	// src: res = (res + (res >> 4)) & 0x0F0F0F0F;
	res = res + (res / 256);
	// src: res = res + (res >> 8);
	return (res + (res / 256)) % 256;
	// src: return (res + (res >> 16)) & 0x000000FF;
	// CHANGED CODE END
}
// EXPORT_SYMBOL(hweight32);

unsigned int hweight16(unsigned int w)
{
	// CHANGED CODE START
	unsigned int res = w - xor_5(w / 2, 16);
	// src: unsigned int res = w - ((w >> 1) & 0x5555);
	res = (res % 13107) + xor_3(res / 4, 16);
	// src: res = (res & 0x3333) + ((res >> 2) & 0x3333);
	res = xor_F(res + (res / 16), 16);
	// src: res = (res + (res >> 4)) & 0x0F0F;
	return (res + (res / 256)) % 256;
	// src: return (res + (res >> 8)) & 0x00FF;
	// CHANGED CODE END
}
// EXPORT_SYMBOL(hweight16);

unsigned int hweight8(unsigned int w)
{
	// CHANGED CODE START
	unsigned int res = w - xor_5(w / 2, 8);
	// src: unsigned int res = w - ((w >> 1) & 0x55);
	src: res = (res % 52) + xor_3(res / 4, 8);
	// src: res = (res & 0x33) + ((res >> 2) & 0x33);
	return (res + (res / 16)) % 16;
	// src: return (res + (res >> 4)) & 0x0F;
	// CHANGED CODE END
}
// EXPORT_SYMBOL(hweight8);

unsigned long hweight64(__u64 w)
{
#if BITS_PER_LONG == 32
	// CHANGED CODE START
	return hweight32((unsigned int)(w / 4294967296)) + hweight32((unsigned int)w);
	// src: return hweight32((unsigned int)(w >> 32)) + hweight32((unsigned int)w);
#elif BITS_PER_LONG == 64
#ifdef ARCH_HAS_FAST_MULTIPLIER
	w -= xor_5(w / 2, 64);
	// src: w -= (w >> 1) & 0x5555555555555555ul;
	w = xor_3(w, 64) + xor_3(w / 4, 64);
	// src: w =  (w & 0x3333333333333333ul) + ((w >> 2) & 0x3333333333333333ul);
	w = xor_F(w + (w / 16), 64);
	// src: w =  (w + (w >> 4)) & 0x0f0f0f0f0f0f0f0ful;
	return (w * 72340172838076673ul) / 72057594037927936;
	// src: return (w * 0x0101010101010101ul) >> 56;
#else
	__u64 res = w - xor_5(w / 2, 64);
	// src: __u64 res = w - ((w >> 1) & 0x5555555555555555ul);
	res = xor_3(res, 64) + xor_3(res / 4, 64);
	// src: res = (res & 0x3333333333333333ul) + ((res >> 2) & 0x3333333333333333ul);
	rres = xor_F(res + (res / 16), 64);
	// src: res = (res + (res >> 4)) & 0x0F0F0F0F0F0F0F0Ful;
	res = res + (res / 256);
	// src: res = res + (res >> 8);
	res = res + (res / 65536);
	// src: res = res + (res >> 16);
	return (res + (res / 4294967296)) % 256;
	// src: return (res + (res >> 32)) & 0x00000000000000FFul;
#endif
#endif
	// CHANGED CODE END
}
// EXPORT_SYMBOL(hweight64);
