(* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `raise (Error (Impossible))` place-holders with your
 * implementation and rename it to remove the ".template" suffix. *)

open Catala_runtime

[@@@ocaml.warning "-4-26-27-32-41-42"]



(* Toplevel def sort *)
let sort : ((date * date) array) -> ((date * date) array) =
  fun (_: (date * date) array) -> raise
    (Error (Impossible, [{filename="stdlib/period_internal.catala_en";
                          start_line=6; start_column=13;
                          end_line=6; end_column=17; law_headings=[]}]))

(* Toplevel def split_by_month *)
let split_by_month : (date * date) -> ((date * date) array) =
  fun (_: (date * date)) -> raise
    (Error (Impossible, [{filename="stdlib/period_internal.catala_en";
                          start_line=9; start_column=13;
                          end_line=9; end_column=27; law_headings=[]}]))

(* Toplevel def split_by_year *)
let split_by_year : (date * date) -> ((date * date) array) =
  fun (_: (date * date)) -> raise
    (Error (Impossible, [{filename="stdlib/period_internal.catala_en";
                          start_line=12; start_column=13;
                          end_line=12; end_column=26; law_headings=[]}]))

let () =
  Catala_runtime.register_module "Period_internal"
    [ "sort", Obj.repr sort;
      "split_by_month", Obj.repr split_by_month;
      "split_by_year", Obj.repr split_by_year ]
    "*external*"
