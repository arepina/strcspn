#ifndef __STRCSPN_H__
#define __STRCSPN_H__

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
    }
 */

#endif // __STRCSPN_H__
