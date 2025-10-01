(* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `raise (Error (Impossible))` place-holders with your
 * implementation and rename it to remove the ".template" suffix. *)

[@@@ocaml.warning "-4-26-27-32-33-34-37-41-42-69"]

open Catala_runtime



(* Toplevel def sequence *)
let sequence : integer -> integer -> (integer array) =
  fun (_: integer) (_: integer) -> raise
    (Error (Impossible, [{filename="stdlib/list_internal.catala_en";
                          start_line=4; start_column=13;
                          end_line=4; end_column=21; law_headings=[]}]))

(* Toplevel def nth_element *)
let nth_element : ('t array) -> integer -> ('t) Optional.t =
  raise
  (Error (Impossible, [{filename="stdlib/list_internal.catala_en";
                        start_line=9; start_column=13;
                        end_line=9; end_column=24; law_headings=[]}]))

(* Toplevel def remove_nth_element *)
let remove_nth_element : ('t array) -> integer -> ('t array) =
  raise
  (Error (Impossible, [{filename="stdlib/list_internal.catala_en";
                        start_line=14; start_column=13;
                        end_line=14; end_column=31; law_headings=[]}]))

let () =
  Catala_runtime.register_module "List_internal"
    [ "sequence", Obj.repr sequence;
      "nth_element", Obj.repr nth_element;
      "remove_nth_element", Obj.repr remove_nth_element ]
    "*external*"
