#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <inttypes.h>
#include <gc.h>

uint32_t pcf_print(uint32_t x) {
	printf("%" PRIu32 "\n", x);
	return x;
}

void *pcf_mkclosure(void *fun, int amt, ...)
{
	int i;
	va_list valist;
	uint64_t** res = GC_MALLOC(sizeof (uint64_t*) * (amt + 1));

	va_start(valist, amt);

	res[0] = fun;
	i = 0;
	while (i++ < amt) {
		uint64_t *a = va_arg(valist, uint64_t*);
		res[i] = a;
	}

	va_end(valist);

	return res;
}

extern uint64_t* pcfmain(void);

int main (int argc, char **argv) {
	uint64_t* rp = pcfmain();
	uint64_t r = (uint64_t)rp;

	pcf_print(r);

	return r;
}
