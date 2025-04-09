(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2025 Inria,
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

(** Our parser crosses the bounds of LR parsing for two features:
    - attaching breadcrumbs to every position (leading titles, subtitles, etc.)
    - making the comments available where wanted

    for these purposes we maintain a little bit of state and contained
    side-effects:
    -> parser calls MUST be done within the `with_state` function
 *)

type t

val with_state : (Sedlexing.lexbuf -> 'a) -> Sedlexing.lexbuf -> 'a
(** Mandatory wrapper around parser calls *)

val new_heading :
  string * string option * bool * int ->
  Lexing.position * Lexing.position ->
  Ast.law_heading

val get_current_heading : unit -> string list

(** Comments handling (this doesn't concern attributes):

    In order to not overload the parser with support for a comment token
    everywhere, the parser driver skips those, but they are registered here
    using [reset_comments] and [add_comment]. Then, specific parser rules where
    they make sense can retrieve them using [get_comments].

    Note that the comments are only available to the immediately following
    token.
*)

val reset_comments : unit -> unit
val add_comment : string -> unit
val get_comments : unit -> string list
