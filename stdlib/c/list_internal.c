/* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `catala_error(catala_impossible)` place-holders with
 * your implementation and rename it to remove the ".template" suffix. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <catala_runtime.h>

const CATALA_ARRAY(CATALA_INT) ListInternal__sequence
    (CATALA_INT begin, CATALA_INT end)
{
  mpz_t zlen;
  size_t i, len;
  catala_array* ret = catala_malloc(sizeof(catala_array));
  mpz_init (zlen);
  mpz_sub (zlen, end, begin);
  len = mpz_sgn (zlen) > 0 ? mpz_get_ui (zlen) : 0;
  mpz_clear (zlen);
  printf ("%ld..%ld (%lu)\n", mpz_get_si(begin), mpz_get_si(end), len);
  ret->size = len;
  ret->elements = catala_malloc(len * sizeof(CATALA_INT));
  for (i = 0; i < len; i++) {
    mpz_t x;
    mpz_init (x);
    mpz_add_ui (x, begin, i);
    ret->elements[i] = x;
    printf ("     %02lu -- %ld\n", i, mpz_get_si (x));
  }
  return ret;
}

const CATALA_OPTION(void * /* any t */) ListInternal__nth_element
    (const CATALA_ARRAY(void * /* any t */) lst, CATALA_INT index)
{
  int n = mpz_get_si (index) - 1;
  if (0 <= n && n < lst->size)
    return catala_some(lst->elements[n]);
  else
    return CATALA_NONE;
}

const CATALA_ARRAY(void * /* any t */) ListInternal__remove_nth_element
    (const CATALA_ARRAY(void * /* any t */) lst, CATALA_INT index)
{
  int n = mpz_get_si (index) - 1;
  if (0 <= n && n < lst->size) {
    int i;
    size_t len = lst->size;
    catala_array* ret = catala_malloc(sizeof(catala_array));
    ret->size = len - 1;
    ret->elements = catala_malloc (ret->size * sizeof(void*));
    for (i = 0; i < n; i++)
      ret->elements[i] = lst->elements[i];
    for (i = n+1; i < len; i++)
      ret->elements[i-1] = lst->elements[i];
    return ret;
  } else {
    return lst;
  }
}
