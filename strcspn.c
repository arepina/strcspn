#include "strcspn.h"

/*@ axiomatic Strcspn {

    logic size_t strcspn(char *s, char *reject);

		lemma strcspn_shift:
       \forall char *s, *reject;
          valid_str(s) && valid_str(reject) && *s != '\0'
					&& (\forall char *r; reject <= r < reject + strlen(reject) ==> *r != *s)
					==> strcspn(s, reject) == 1 + strcspn(s + 1, reject);

		lemma strcspn_pointers:
			 \forall char *s, *sc, *reject;
					valid_str(s)  && valid_str(sc) &&
					\base_addr(s) == \base_addr(sc) &&
					s <= sc < s + strlen(s)
					==> strcspn(sc, reject) <= strcspn(s, reject);

		lemma strcspn_all_chars:
       \forall char* s, *reject, *sc;
          valid_str(s) && valid_str(reject) && *s != '\0' && s <= sc < s + strlen(s)
					&& (\forall char *r; reject <= r < reject + strlen(reject) ==> *r != *sc)
					==> strcspn(s, reject) == strlen(s);

    lemma strcspn_zero_s:
       \forall char* s, *reject;
				 valid_str(s) && valid_str(reject) && strlen(s) == 0
				 ==> strcspn(s, reject) == 0;

	 lemma strcspn_zero_reject:
			\forall char* s, *reject;
				valid_str(s) && valid_str(reject) && strlen(reject) == 0
				==> strcspn(s, reject) == strlen(s);

		lemma strcspn_less:
				\forall char* s, *reject;
					valid_str(s) && valid_str(reject) && *s != '\0'
					==> strcspn(s, reject) <= strlen(s);

	}
*/


/*@ requires valid_str(s);
    requires valid_str(reject);
		requires \forall char *sc; s <= sc < s + strlen(s) ==> *sc != '\0';
		requires \forall char *r; reject <= r < reject + strlen(reject) ==> *r != '\0';
    assigns \nothing;
		ensures \forall char *t, integer i; 0 <= i < \result && reject <= t < reject + strlen(reject) ==> s[i] != *t;
		ensures \result == strcspn(s, reject);
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
			loop invariant \forall char *z, *t; s <= z < p && reject <= t < reject + strlen(reject) ==> *z != *t;
			//loop invariant strcspn(s, reject) >= strcspn(p, reject) + count;
			loop assigns count, p, r;
      loop variant strlen(s) - (p - s);
 */
	for (p = s; *p != '\0'; ++p) {
    /*@ loop invariant \base_addr(reject) == \base_addr(r);
				loop invariant valid_str(r);
				loop invariant reject <= r <= reject + strlen(reject);
				loop invariant strlen(reject) == strlen(r) + (r - reject);
				loop invariant \forall char *t; reject <= t < r ==> *p != *t;
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
