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

module Make(Arg: Arg)() = struct
  let fresh_id =
    let count = ref 0 in
    fun () ->
      let n = !count in
      incr count;
      n

  module M = struct
    type t = {
      id: int;
      name: string;
      pos: Pos.t;
    }

    let compare x y = Int.compare x.id y.id
    let equal x y = Int.equal x.id y.id
    let hash x = x.id
    let format ppf x =
      Format.pp_open_stag ppf (Ocolor_format.Ocolor_style_tag Arg.style);
      Format.pp_print_string ppf x.name;
      (* Format.pp_print_int ppf t.id; (* uncomment for precise uid debug *) *)
      Format.pp_close_stag ppf ()
  end
  include M

  module Set = Set.Make(M)
  module Map = Map.Make(M)

  let make ~pos name = {
    id = fresh_id ();
    name; pos
  }
  let name x = x.name
  let id x = x.id
  let pos x = x.pos
  let fresh ?(name="_") ?(pos=Pos.void) () = {
    id = fresh_id ();
    name;
    pos
  }

  let refresh x = { x with id = fresh_id() }
  let rename x name = { x with name }

  type var = t
  module Subst = struct
    type nonrec t = t Map.t
    let empty = Map.empty
    let single = Map.singleton
    let add subst x y =
      if equal x y then subst
      else Map.add x y subst
    let merge subst1 subst2 =
      Map.union (fun _ _ _ -> Message.error ~internal:true "Variable substitution error") subst1 subst2

    let apply subst x =
      match Map.find_opt x subst with
      | Some y -> y
      | None -> x

    let check_capture subst set =
      let keys =
        Map.fold (fun k _ -> Set.add k)
          subst Set.empty
      in
      assert (Set.disjoint keys set)
  end
end
