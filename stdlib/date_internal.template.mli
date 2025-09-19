(* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `raise (Error (Impossible))` place-holders with your
 * implementation and rename it to remove the ".template" suffix. *)

[@@@ocaml.warning "-4-26-27-32-33-34-37-41-42-69"]

open Catala_runtime


module Stdlib_en
  = Stdlib_en
module Date_en = Date_en
module Period_en = Period_en
module Money_en = Money_en
module Integer_en = Integer_en
module Decimal_en = Decimal_en


(** Toplevel definition of_ymd *)
val of_ymd : code_location -> integer -> integer -> integer -> date

(** Toplevel definition to_ymd *)
val to_ymd : date -> (integer * integer * integer)

(** Toplevel definition last_day_of_month *)
val last_day_of_month : date -> date
