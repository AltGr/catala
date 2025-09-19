#include <stdio.h>
#include <stdlib.h>
#include <catala_runtime.h>


/* static const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/))(*
 *            period_internal__sort_init)
 *            (const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/)))
 *     ()
 * {
 *   static const catala_code_position pos[1] =
 *     {{"stdlib/period_internal.catala_en", 6, 13, 6, 17}};
 *   catala_error(catala_impossible, pos, 1);
 *   /\* TODO *\/
 *   abort();
 * }
 * 
 * const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/))(*
 *     PeriodInternal__sort)
 *     (const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/))) () {
 *   static const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/))(*
 *              PeriodInternal__sort)
 *              (const CATALA_ARRAY(CATALA_TUPLE(CATALA_TUPLE(CATALA_DATE;CATALA_DATE);void * /\* any t *\/))) = NULL;
 *   return CATALA_GET_LAZY(PeriodInternal__sort, period_internal__sort_init());
 * } */

const CATALA_ARRAY(CATALA_TUPLE(CATALA_DATE;CATALA_DATE))
    PeriodInternal__split_by_month
    (const CATALA_TUPLE(CATALA_DATE;CATALA_DATE) p)
{
  static const catala_code_position pos[1] =
    {{"stdlib/period_internal.catala_en", 10, 13, 10, 27}};
  catala_error(catala_impossible, pos, 1);
  /* TODO */
  abort();
}

const CATALA_ARRAY(CATALA_TUPLE(CATALA_DATE;CATALA_DATE))
    PeriodInternal__split_by_year
    (CATALA_INT start_month, const CATALA_TUPLE(CATALA_DATE;CATALA_DATE) p)
{
  static const catala_code_position pos[1] =
    {{"stdlib/period_internal.catala_en", 12, 13, 12, 26}};
  catala_error(catala_impossible, pos, 1);
  /* TODO */
  abort();
}

