(* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `raise (Error (Impossible))` place-holders with your
 * implementation and rename it to remove the ".template" suffix. *)

open Catala_runtime

[@@@ocaml.warning "-4-26-27-32-41-42"]



(** Toplevel definition sort *)
val sort : ((date * date) array) -> ((date * date) array)

(** Toplevel definition split_by_month *)
val split_by_month : ((date * date) array) -> ((date * date) array)

(** Toplevel definition split_by_year *)
val split_by_year : ((date * date) array) -> ((date * date) array)
