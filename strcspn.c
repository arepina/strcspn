#include "strcspn.h"

/*@ requires valid_str(s);
    requires valid_str(reject);
    assigns \nothing;
 */
size_t strcspn(const char *s, const char *reject)
{
	const char *p;
	const char *r;
	size_t count = 0;
  /*@ loop invariant \base_addr(s) == \base_addr(p);
	    loop invariant valid_str(p);
      loop invariant 0 <= count <= strlen(s);
			loop invariant count == p - s;
      loop invariant s <= p <= s + strlen(s);
      loop invariant strlen(s) == strlen(p) + (p - s);
			loop assigns count, p, r;
      loop variant strlen(s) - (p - s);
 */
	for (p = s; *p != '\0'; ++p) {
    /*@ loop invariant \base_addr(reject) == \base_addr(r);
				loop invariant valid_str(r);
				loop invariant reject <= r <= reject + strlen(reject);
				loop invariant strlen(reject) == strlen(r) + (r - reject);
        loop variant strlen(reject) - (r - reject);
    */
		for (r = reject; *r != '\0'; ++r) {
			if (*p == *r)
        //@ assert *p == *r;
				return count;
		}
		//@ghost Before:
		++count;
		 //@ assert \at(count + 1, Before) == \at(count, Here);
	}
	return count;
}

int main(void)
{
    printf("%d\n", strcspn("123", "4"));
    return 0;
}
