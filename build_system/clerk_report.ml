(* This file is part of the Catala build system, a specification language for
   tax and social benefits computation rules. Copyright (C) 2024 Inria,
   contributors: Louis Gesbert <louis.gesbert@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

(** This module defines and manipulates Clerk test reports, which can be written
    by `clerk runtest` and read to provide test result summaries. This only
    concerns inline tests (```catala-test-inline blocks). *)

open Catala_utils

type test = {
  success: bool;
  command_line: string list;
  expected: Lexing.position * Lexing.position;
  result: Lexing.position * Lexing.position;
}

type file = {
  name : File.t;
  successful : int;
  total : int;
  tests : test list
}

let write_to f file =
  File.with_out_channel f
    (fun oc -> Marshal.to_channel oc (file: file) [])

let read_from f =
  File.with_in_channel f Marshal.from_channel

let read_many f =
  File.with_in_channel f @@ fun ic ->
  let rec results () =
    match Marshal.from_channel ic with
    | file -> file :: results ()
    | exception End_of_file -> []
  in
  results ()

let has_command cmd =
  let check_cmd = Printf.sprintf "type %s >/dev/null 2>&1" cmd in
  Sys.command check_cmd = 0

let diff_command =
  lazy
    (if has_command "patdiff" && Message.has_color stdout && false then
       fun _columns -> ["patdiff"; "-alt-old"; "expected"; "-alt-new"; "result"]
     else
       fun columns -> [
         "diff";
         "-y"; "-t"; (* "--suppress-common-lines"; "--horizon-lines=3"; *)
         "-W"; string_of_int (columns - 5);
         (* "-b"; *)
         "--color="^(if Message.has_color stdout then "always" else "never");
         "--label";
         "expected";
         "--label";
         "result";
       ])

let get_diff ~columns p1 p2 =
  let get_str (pstart, pend) =
    assert (pstart.Lexing.pos_fname = pend.Lexing.pos_fname);
    File.with_in_channel pstart.Lexing.pos_fname @@ fun ic ->
    seek_in ic pstart.Lexing.pos_cnum;
    really_input_string ic (pend.Lexing.pos_cnum - pstart.Lexing.pos_cnum)
  in
  File.with_temp_file "clerk-diff" "a" ~contents:(get_str p1)
  @@ fun f1 ->
  File.with_temp_file "clerk_diff" "b" ~contents:(get_str p2)
  @@ fun f2 ->
  match Lazy.force diff_command columns with
  | [] -> assert false
  | cmd :: args -> File.process_out ~check_exit:(fun _ -> ()) cmd (args @ [f1; f2])

let display ~columns ~build_dir ppf t =
  let pfile f =
    f |>
    String.remove_prefix ~prefix:(build_dir ^ Filename.dir_sep) |>
    String.remove_prefix ~prefix:(Sys.getcwd () ^ Filename.dir_sep)
  in
  let command_line_cleaned =
    List.filter_map (fun s ->
        if s = "--directory="^build_dir then None
        else Some (pfile s))
      t.command_line
  in
  let pp_pos ppf (start, stop) =
    assert (start.Lexing.pos_fname = stop.Lexing.pos_fname);
    Format.fprintf ppf "@{<cyan>%s:%d-%d@}"
      (pfile start.Lexing.pos_fname) start.Lexing.pos_lnum stop.Lexing.pos_lnum
  in
  if t.success then
    Format.fprintf ppf "@{<green>■@} %a passed" pp_pos t.expected
      (* ● *)
  else
    (Format.pp_open_vbox ppf 2;
     Format.fprintf ppf
       "@{<red>■@} %a failed@," pp_pos t.expected;
     Format.fprintf ppf
       "@[<h>$ @{<yellow>%a@}@]@," (Format.pp_print_list ~pp_sep:Format.pp_print_space Format.pp_print_string)
       command_line_cleaned;
     get_diff ~columns t.expected t.result |> String.trim |> String.split_on_char '\n' |>
     Format.pp_print_list Format.pp_print_string ppf;
     Format.pp_close_box ppf ())

let display_file ~columns ~build_dir ppf t =
  let pfile f = String.remove_prefix ~prefix:(build_dir ^ Filename.dir_sep) f in
  if t.successful = t.total then
    Format.fprintf ppf "@{<bg_green>  @} @{<cyan>%s@}: @{<green>%d@} / %d tests passed@," (pfile t.name) t.successful t.total
  else
    ((function 0 -> Format.fprintf ppf "@{<bg_red>  @}" | _ -> Format.fprintf ppf "@{<bg_yellow>  @}") t.successful;
     Format.fprintf ppf " @{<cyan>%s@}: " (pfile t.name);
     (function 0 -> Format.fprintf ppf "@{<red>0@}" | n -> Format.fprintf ppf "@{<yellow>%d@}" n) t.successful;
     Format.fprintf ppf " / %d tests passed" t.total;
     Format.pp_print_break ppf 0 3;
     Format.pp_open_vbox ppf 0;
     Format.pp_print_list (display ~columns ~build_dir) ppf t.tests;
     Format.pp_close_box ppf ();
     Format.pp_print_cut ppf ())

let summary ~columns ~build_dir tests =
  let ppf = Message.formatter_of_out_channel stdout () in
  Format.pp_open_vbox ppf 0;
  let files, success_files, success, total =
    List.fold_left (fun (files, success_files, success, total) file ->
        files + 1, (if file.successful < file.total then success_files else success_files + 1), success + file.successful, total + file.total)
      (0, 0, 0, 0) tests
  in
  List.iter (fun f -> display_file ~columns ~build_dir ppf f) tests;
  if success < total then
    (Format.fprintf ppf "@,@{<red>┏%s @{<bg_red;bold;rgb(0,0,0)> TESTS FAILED @} %s┓@}@,"
       (String.repeat ((columns - 18) / 2) "━")
       (String.repeat (columns - 18 - (columns - 18) / 2) "━");
     Format.pp_open_tbox ppf ();
     Format.fprintf ppf "@{<red>@<1>%s@}%*s" "┃" (columns - 2) "";
     Format.pp_set_tab ppf ();
     Format.fprintf ppf "@{<red>┃@}@,";
     Format.fprintf ppf "@{<red>@<1>%s@}  %d tests from %d files failed"
       "┃"
       (total - success)
       (files - success_files);
     Format.pp_print_tab ppf ();
     Format.fprintf ppf "@{<red>┃@}@,";
     Format.fprintf ppf "@{<red>@<1>%s@}  @{<green>%d@} / %d tests passed from a total of %d files"
       "┃"
       success
       total files;
     Format.pp_print_tab ppf ();
     Format.fprintf ppf "@{<red>┃@}@,";
     Format.fprintf ppf "@{<red>@<1>%s@}" "┃";
     Format.pp_print_tab ppf ();
     Format.fprintf ppf "@{<red>┃@}@,";
     Format.pp_close_tbox ppf ();
     Format.fprintf ppf "@{<red>┗%s┛@}@,"
        (String.repeat (columns - 2) "━")
    )
  else
    (Format.fprintf ppf "@,@{<green>┏%s @{<bg_green;bold;rgb(0,0,0)> ALL TESTS PASSED @} %s┓@}@,"
       (String.repeat ((columns - 22) / 2) "━")
       (String.repeat (columns - 22 - (columns - 22) / 2) "━");
     Format.pp_open_tbox ppf ();
     Format.fprintf ppf "@{<green>@<1>%s@}%*s" "┃" (columns - 2) "";
     Format.pp_set_tab ppf ();
     Format.fprintf ppf "@{<green>┃@}@,";
      Format.fprintf ppf "@{<green>@<1>%s@}  @{<green>%d@} / %d tests across @{<green>%d@} files passed" "┃" success total files;
     Format.pp_print_tab ppf ();
     Format.fprintf ppf "@{<green>┃@}@,";
     Format.fprintf ppf "@{<green>@<1>%s@}" "┃";
     Format.pp_print_tab ppf ();
     Format.fprintf ppf "@{<green>┃@}@,";
     Format.pp_close_tbox ppf ();
     Format.fprintf ppf "@{<green>┗%s┛@}@,"
        (String.repeat (columns - 2) "━"));
  Format.pp_close_box ppf ();
  Format.pp_print_flush ppf ();
  success = total
