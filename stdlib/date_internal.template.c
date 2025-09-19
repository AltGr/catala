/* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `catala_error(catala_impossible)` place-holders with
 * your implementation and rename it to remove the ".template" suffix. */

#include <stdio.h>
#include <stdlib.h>
#include <catala_runtime.h>

#include <Stdlib_en.h>
#include <Date_en.h>
#include <Period_en.h>
#include <Money_en.h>
#include <Integer_en.h>
#include <Decimal_en.h>

CATALA_DATE DateInternal__of_ymd
    (CATALA_POSITION pos,
     CATALA_INT dyear,
     CATALA_INT dmonth,
     CATALA_INT dday)
{
  static const catala_code_position pos__1[1] =
    {{"stdlib/date_internal.catala_en", 4, 13, 4, 19}};
  catala_error(catala_impossible, pos__1, 1);
  abort();
}

const CATALA_TUPLE(CATALA_INT;CATALA_INT;CATALA_INT) DateInternal__to_ymd
    (CATALA_DATE d)
{
  static const catala_code_position pos[1] =
    {{"stdlib/date_internal.catala_en", 11, 13, 11, 19}};
  catala_error(catala_impossible, pos, 1);
  abort();
}

CATALA_DATE DateInternal__last_day_of_month (CATALA_DATE d)
{
  static const catala_code_position pos[1] =
    {{"stdlib/date_internal.catala_en", 15, 13, 15, 30}};
  catala_error(catala_impossible, pos, 1);
  abort();
}

