(* This is a template file following the expected interface and declarations to
 * implement the corresponding Catala module.
 *
 * You should replace all `raise (Error (Impossible))` place-holders with your
 * implementation and rename it to remove the ".template" suffix. *)

[@@@ocaml.warning "-4-26-27-32-33-34-37-41-42-69"]

open Catala_runtime


let () =
  match Catala_runtime.check_module "Stdlib_en" "CM0|3a5cb3ee|32e49b03|165aeded"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Stdlib_en, it may need recompiling"
module Stdlib_en = Stdlib_en
let () =
  match Catala_runtime.check_module "Date_en" "CM0|3a5cb3ee|32e49b03|248f37a9"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Date_en, it may need recompiling"
module Date_en = Date_en
let () =
  match Catala_runtime.check_module "Period_en" "CM0|3a5cb3ee|32e49b03|20244978"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Period_en, it may need recompiling"
module Period_en = Period_en
let () =
  match Catala_runtime.check_module "Money_en" "CM0|3a5cb3ee|32e49b03|326fa269"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Money_en, it may need recompiling"
module Money_en = Money_en
let () =
  match Catala_runtime.check_module "Integer_en" "CM0|3a5cb3ee|32e49b03|002b72fa"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Integer_en, it may need recompiling"
module Integer_en = Integer_en
let () =
  match Catala_runtime.check_module "Decimal_en" "CM0|3a5cb3ee|32e49b03|3ec2f50d"
    with
  | Ok () -> ()
  | Error h -> failwith "Hash mismatch for module Decimal_en, it may need recompiling"
module Decimal_en = Decimal_en


(* Toplevel def of_ymd *)
let of_ymd : code_location -> integer -> integer -> integer -> date =
  fun (_: code_location) (_: integer) (_: integer) (_: integer) -> raise
    (Error (Impossible, [{filename="stdlib/date_internal.catala_en";
                          start_line=4; start_column=13;
                          end_line=4; end_column=19; law_headings=[]}]))

(* Toplevel def to_ymd *)
let to_ymd : date -> (integer * integer * integer) =
  fun (_: date) -> raise
    (Error (Impossible, [{filename="stdlib/date_internal.catala_en";
                          start_line=11; start_column=13;
                          end_line=11; end_column=19; law_headings=[]}]))

(* Toplevel def last_day_of_month *)
let last_day_of_month : date -> date =
  fun (_: date) -> raise
    (Error (Impossible, [{filename="stdlib/date_internal.catala_en";
                          start_line=15; start_column=13;
                          end_line=15; end_column=30; law_headings=[]}]))

let () =
  Catala_runtime.register_module "Date_internal"
    [ "of_ymd", Obj.repr of_ymd;
      "to_ymd", Obj.repr to_ymd;
      "last_day_of_month", Obj.repr last_day_of_month ]
    "*external*"
