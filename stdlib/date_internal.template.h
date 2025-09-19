/* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `catala_error(catala_impossible)` place-holders with
 * your implementation and rename it to remove the ".template" suffix. */

#ifndef __DATE_INTERNAL_H__
#define __DATE_INTERNAL_H__

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
     CATALA_INT dday);

const CATALA_TUPLE(CATALA_INT;CATALA_INT;CATALA_INT) DateInternal__to_ymd
    (CATALA_DATE d);

CATALA_DATE DateInternal__last_day_of_month (CATALA_DATE d);

#endif /* __DATE_INTERNAL_H__ */
