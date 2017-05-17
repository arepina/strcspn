#pragma once

typedef unsigned long __kernel_ulong_t;
typedef __kernel_ulong_t __kernel_size_t;
typedef __kernel_size_t size_t;


/*@ axiomatic Strlen {
    predicate valid_str(char *s) =
       \exists size_t n;
          s[n] == '\0' && \valid(s+(0..n));

    lemma valid_str_shift1:
       \forall char *s;
       *s != '\0' &&
       valid_str(s) ==> valid_str(s+1);

    logic size_t strlen(char *s) =
       s[0] == '\0' ? (size_t) 0 : (size_t) ((size_t)1 + strlen(s + 1));

    lemma strlen_before_null:
       \forall char* s, integer i;
          valid_str(s) &&
          0 <= i < strlen(s) ==> s[i] != '\0';

    lemma strlen_at_null:
       \forall char* s;
          valid_str(s) ==> s[strlen(s)] == '\0';

    lemma strlen_shift:
       \forall char *s, size_t i;
          valid_str(s) &&
          i <= strlen(s) ==>
          strlen(s+i) == strlen(s)-i;

    lemma strlen_shift_ex:
       \forall char *s, size_t i;
          valid_str(s) &&
          0 < i <= strlen(s) ==>
          strlen(s+i) < strlen(s);

    lemma strlen_shift1:
       \forall char *s;
          valid_str(s) && *s != '\0' ==>
          strlen(s) == 1 + strlen(s+1);

    lemma strlen_pointers:
       \forall char *s, *sc;
          valid_str(s)  &&
          valid_str(sc) &&
          \base_addr(s) == \base_addr(sc) &&
          s <= sc &&
          (\forall integer i; 0 <= i <= sc - s ==> s[i] != '\0') ==>
             strlen(sc) <= strlen(s);

    lemma strlen_main:
       \forall char *s, size_t n;
       valid_str(s) &&
       s[n] == '\0' &&
       (\forall size_t i; i < n ==> s[i] != '\0') ==>
           strlen(s) == n;

   logic boolean in_array(char *s, char val) = *s == '\0' ? \false : (*s == val ? \true : in_array(s+1, val));

   lemma in_array_shift1:
     \forall char* s, val; valid_str(s) && *s != '\0' && *s != val && val != '\0' ==>
     in_array(s, val) == in_array(s+1, val);

   lemma in_array_at_null:
        \forall char* s, val;
         *s == '\0' && val != '\0' ==> in_array(s, val) == \false;

   lemma in_array_shift2:
       \forall char* s, val; valid_str(s) && *s != '\0' && *s == val && val != '\0' ==>
           in_array(s, val) == \true;
    }
 */

//____________________________________________________________________________________________________________________________________________

 /*@ axiomatic Strcspn {

     logic size_t strcspn(char *s, char *reject);

 		lemma strcspn_shift:
        \forall char *s,*reject;
           valid_str(s) && valid_str(reject) && *s != '\0' && !in_array(reject,*s) ==>
           strcspn(s, reject) == 1 + strcspn(s + 1, reject);

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

 		lemma strspn_at_null:
 	     \forall char* s,*reject;
 	      *s == '\0' ==> strcspn(s, reject) == 0;

 		lemma strcspn_less:
 				\forall char* s, *reject;
 					valid_str(s) && valid_str(reject) && *s != '\0'
 					==> strcspn(s, reject) <= strlen(s);

 	}
 */

 /*@ requires valid_str(s);
     requires valid_str(reject);
     assigns \nothing;
 		ensures \forall char *t, integer i; 0 <= i < \result && reject <= t < reject + strlen(reject) ==> s[i] != *t;
 		ensures \result == strcspn(s, reject);
  */
 size_t strcspn(const char *s, const char *reject);
