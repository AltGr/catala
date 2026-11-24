(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020-2022 Inria,
   contributor: Louis Gesbert <louis.gesbert@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

open Catala_utils

module type Arg = sig
  val style: Ocolor_types.style
end

(** {1 Variables and their collections} *)
module Make(Arg: Arg) (): sig

  type t

  val make : pos:Pos.t -> string -> t
  (** The position is expected to be the declaration or the first appearance of the variable *)

  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val name : t -> string
  val id : t -> int
  val pos : t -> Pos.t
  val format : Format.formatter -> t -> unit
  val fresh : ?name:string -> ?pos:Pos.t -> unit -> t
  val refresh : t -> t
  val rename : t -> string -> t

  module Set: Set.S with type elt = t
  module Map: Map.S with type key = t

  type var = t
  module Subst: sig
    type t

    val empty : t
    val single : var -> var -> t
    val add : t -> var -> var -> t
    val merge : t -> t -> t
    val apply : t -> var -> var
    val check_capture : t -> Set.t -> unit
  end
end
