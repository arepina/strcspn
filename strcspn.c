#include "strcspn.h"


size_t strcspn(const char *s, const char *reject)
{
	const char *p;
	const char *r;
	size_t count = 0;
    /*@ loop invariant \base_addr(p) == \base_addr(s);
	    loop variant strlen(s) - (p - s);
     */
	for (p = s; *p != '\0'; ++p) {
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r)
				return count;
		}
		++count;
	}
	return count;
}

#ifdef OUT_OF_TASK
#include <stdio.h>

int main(void)
{
    char str [10]=”0123456789”;
    char sym [10]=”9876”;
    printf ("%d\n”,strcspn (str,sym));
    return 0;
}

#endif
