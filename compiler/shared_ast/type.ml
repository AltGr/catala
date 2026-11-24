(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Louis Gesbert <louis.gesbert@inria.fr>

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
open Definitions

type t = typ
type var = tvar

let equal_tlit l1 l2 = l1 = l2
let compare_tlit l1 l2 = Stdlib.compare l1 l2

let rec equal_s (s1, s2 as subst) ty1 ty2 =
  match Mark.remove ty1, Mark.remove ty2 with
  | TLit l1, TLit l2 -> equal_tlit l1 l2
  | TTuple tys1, TTuple tys2 -> equal_list_s subst tys1 tys2
  | TStruct n1, TStruct n2 -> StructName.equal n1 n2
  | TEnum n1, TEnum n2 -> EnumName.equal n1 n2
  | TAbstract n1, TAbstract n2 -> AbstractType.equal n1 n2
  | TOption t1, TOption t2 -> equal_s subst t1 t2
  | TArrow (t1, t1'), TArrow (t2, t2') -> equal_list_s subst t1 t2 && equal_s subst t1' t2'
  | TArray t1, TArray t2 -> equal_s subst t1 t2
  | TDefault t1, TDefault t2 -> equal_s subst t1 t2
  | TVar tv1, TVar tv2 ->
    TVar.equal (TVar.Subst.apply s1 tv1) (TVar.Subst.apply s2 tv2)
  | TForAll (tv1, t1), TForAll (tv2, t2) ->
    let v = TVar.refresh tv1 in
    equal_s (TVar.Subst.add s1 tv1 v, TVar.Subst.add s2 tv2 v) t1 t2
  | TClosureEnv, TClosureEnv -> true
  | TError, TError -> true
  | ( ( TLit _ | TTuple _ | TStruct _ | TEnum _ | TAbstract _ | TOption _
      | TArrow _ | TArray _ | TDefault _ | TForAll _ | TVar _ | TClosureEnv
      | TError ),
      _ ) ->
    false

and equal_list_s subst tys1 tys2 =
  try List.for_all2 (equal_s subst) tys1 tys2 with Invalid_argument _ -> false

let equal = equal_s (TVar.Subst.empty, TVar.Subst.empty)
let equal_list = equal_list_s (TVar.Subst.empty, TVar.Subst.empty)

let rec compare_s subst (ty1 : t) (ty2 : t) =
  match Mark.remove ty1, Mark.remove ty2 with
  | TLit l1, TLit l2 -> compare_tlit l1 l2
  | TTuple tys1, TTuple tys2 -> List.compare compare tys1 tys2
  | TStruct n1, TStruct n2 -> StructName.compare n1 n2
  | TEnum en1, TEnum en2 -> EnumName.compare en1 en2
  | TAbstract en1, TAbstract en2 -> AbstractType.compare en1 en2
  | TOption t1, TOption t2 -> compare_s subst t1 t2
  | TArrow (a1, b1), TArrow (a2, b2) -> (
    match List.compare (compare_s subst) a1 a2 with 0 -> compare_s subst b1 b2 | n -> n)
  | TArray t1, TArray t2 -> compare_s subst t1 t2
  | TVar tv1, TVar tv2 ->
    let s1, s2 = subst in
    TVar.compare (TVar.Subst.apply s1 tv1) (TVar.Subst.apply s2 tv2)
  | TForAll (tv1, t1), TForAll (tv2, t2) ->
    let s1, s2 = subst in
    let v = TVar.refresh tv1 in
    compare_s (TVar.Subst.add s1 tv1 v, TVar.Subst.add s2 tv2 v) t1 t2
  | TClosureEnv, TClosureEnv -> 0
  | TError, TError -> 0
  | TLit _, _ -> -1
  | _, TLit _ -> 1
  | TTuple _, _ -> -1
  | _, TTuple _ -> 1
  | TStruct _, _ -> -1
  | _, TStruct _ -> 1
  | TEnum _, _ -> -1
  | _, TEnum _ -> 1
  | TAbstract _, _ -> -1
  | _, TAbstract _ -> 1
  | TOption _, _ -> -1
  | _, TOption _ -> 1
  | TArrow _, _ -> -1
  | _, TArrow _ -> 1
  | TArray _, _ -> -1
  | _, TArray _ -> 1
  | TDefault _, _ -> -1
  | _, TDefault _ -> 1
  | TVar _, _ -> -1
  | _, TVar _ -> 1
  | TForAll _, _ -> -1
  | _, TForAll _ -> 1
  | TClosureEnv, _ -> -1
  | _, TClosureEnv -> 1
(* | TError, _ -> -1 *)
(* | _, TError -> -1 *)

let compare = compare_s (TVar.Subst.empty, TVar.Subst.empty)

let format = Print.typ

module Var = struct
  include TVar
  module Hashtbl = Hashtbl.Make(TVar)

  let fresh ?pos () = fresh ~name:"'1" ?pos ()
end

let shallow_fold f ty acc =
  let lfold x acc = List.fold_left (fun acc x -> f x acc) acc x in
  Mark.fold
    (function
      | TLit _ | TStruct _ | TEnum _ | TAbstract _ | TClosureEnv | TVar _ -> acc
      | TTuple tl -> lfold tl acc
      | TOption ty | TArray ty | TDefault ty -> f ty acc
      | TArrow (tl, ty) -> lfold tl (f ty acc)
      | TForAll (_, ty) -> f ty acc
      | TError -> acc)
    ty

let rec free_vars (ty : t) =
  match Mark.remove ty with
  | TVar v -> Var.Set.singleton v
  | TForAll (v, ty) ->
    Var.Set.remove v (free_vars ty)
  | _ ->
    shallow_fold
      (fun ty acc -> Var.Set.union acc (free_vars ty))
      ty Var.Set.empty

let rec free_vars_pos = function
  | TVar v, pos -> Var.Map.singleton v pos
  | TForAll (v, ty), _ ->
    Var.Map.remove v (free_vars_pos ty)
  | ty ->
    shallow_fold
      (fun ty acc -> Var.Map.union (fun _ _ x -> Some x) acc (free_vars_pos ty))
      ty Var.Map.empty

let rec unquantify = function
  | TForAll (_, ty), _ -> unquantify ty
  | ty -> ty

let rec unbind = function
  | TForAll (v, t), _ ->
    let vars, t = unbind t in
    v ::  vars, t
  | t -> [], t

let forall vars t pos =
  List.fold_right (fun v t -> TForAll (v, t), pos) vars t

let fresh_var pos = TVar (Var.fresh ~pos ()), pos
let error pos = TError, pos

(* TODO: deprecate and replace with fresh_var *)
let any = fresh_var

let universal pos =
  let v = Var.fresh () in
  TForAll (v, (TVar v, pos)), pos

let is_universal = function
  | TForAll (v1, (TVar v2, _)), _ -> Var.equal v1 v2
  | _ -> false

(* Similar to [equal], but allows TForAll holes *)
let rec unifiable_s (s1, s2 as subst) (ty1 : t) (ty2 : t) =
  match ty1, ty2 with
  | (TVar _, _), (TVar _, _) -> true
  | (TVar tv1, _), ty2 -> not (Var.Set.mem (TVar.Subst.apply s1 tv1) (Var.Set.map (TVar.Subst.apply s2) (free_vars ty2)))
  | ty1, (TVar tv2, _) -> not (Var.Set.mem (TVar.Subst.apply s2 tv2) (Var.Set.map (TVar.Subst.apply s1) (free_vars ty1)))
  | (TForAll (tv1, ty1), _), ty2 ->
    let v = TVar.refresh tv1 in
    unifiable_s (TVar.Subst.add s1 tv1 v, s2) ty1 ty2
  | ty1, (TForAll (tv2, ty2), _) ->
    let v = TVar.refresh tv2 in
    unifiable_s (s1, TVar.Subst.add s2 tv2 v) ty1 ty2
  | (TLit l1, _), (TLit l2, _) -> equal_tlit l1 l2
  | (TTuple tys1, _), (TTuple tys2, _) -> unifiable_list_s subst tys1 tys2
  | (TStruct n1, _), (TStruct n2, _) -> StructName.equal n1 n2
  | (TEnum n1, _), (TEnum n2, _) -> EnumName.equal n1 n2
  | (TAbstract n1, _), (TAbstract n2, _) -> AbstractType.equal n1 n2
  | (TOption t1, _), (TOption t2, _) -> unifiable_s subst t1 t2
  | (TArrow (t1, t1'), _), (TArrow (t2, t2'), _) ->
    unifiable_list_s subst t1 t2 && unifiable_s subst t1' t2'
  | (TArray t1, _), (TArray t2, _) -> unifiable_s subst t1 t2
  | (TDefault t1, _), (TDefault t2, _) -> unifiable_s subst t1 t2
  | (TClosureEnv, _), (TClosureEnv, _) -> true
  | (TError, _), _ | _, (TError, _) -> true
  | ( ( ( TLit _ | TTuple _ | TStruct _ | TEnum _ | TAbstract _ | TOption _
        | TArrow _ | TArray _ | TDefault _ | TClosureEnv ),
        _ ),
      _ ) ->
    false

and unifiable_list_s subst tys1 tys2 =
  try List.for_all2 (unifiable_s subst) tys1 tys2 with Invalid_argument _ -> false

let unifiable = unifiable_s (TVar.Subst.empty, TVar.Subst.empty)
let unifiable_list = unifiable_list_s (TVar.Subst.empty, TVar.Subst.empty)

let map : (t -> t Bindlib.box) -> t -> t Bindlib.box =
 fun f ty ->
  let nty, m = ty in
  let ( @& ) f bty = Bindlib.box_apply (fun ty -> f ty, m) bty in
  match nty with
  | TLit l -> (fun l -> TLit l) @& Bindlib.box l
  | TTuple tl -> (fun tl -> TTuple tl) @& Bindlib.box_list (List.map f tl)
  | TStruct n -> (fun n -> TStruct n) @& Bindlib.box n
  | TEnum n -> (fun n -> TEnum n) @& Bindlib.box n
  | TAbstract n -> (fun n -> TAbstract n) @& Bindlib.box n
  | TOption ty -> (fun ty -> TOption ty) @& f ty
  | TArrow (tl, ty) ->
    Bindlib.box_apply2
      (fun tl ty -> TArrow (tl, ty), m)
      (Bindlib.box_list (List.map f tl))
      (f ty)
  | TArray ty -> (fun ty -> TArray ty) @& f ty
  | TDefault ty -> (fun ty -> TDefault ty) @& f ty
  | TVar tv -> TVar tv, m
  | TForAll (tv, ty) -> TForAll (tv, f ty), m
  | TClosureEnv -> Bindlib.box (TClosureEnv, m)
  | TError -> Bindlib.box (TError, m)

let rec subst s = function
  | TVar v, m -> TVar (TVar.Subst.apply s v), m
  | TForAll (v, _), _ as t ->
    assert (TVar.equal v (TVar.Subst.apply s v)); (* Check for capture *)
    map (subst s) t
  | t -> map (subst s) t

let rec rebox ty = map rebox ty

let hash ~strip (ty : t) =
  let open Hash.Op in
  let rec aux ctx (ty : t) =
    match Mark.remove ty with
    | TLit l -> !`TLit % !(l : typ_lit)
    | TTuple tl -> List.fold_left (fun acc ty -> acc % aux ctx ty) !`TTuple tl
    | TStruct n -> !`TStruct % StructName.hash ~strip n
    | TEnum n -> !`TEnum % EnumName.hash ~strip n
    | TAbstract n -> !`TAbstract % AbstractType.hash ~strip n
    | TOption ty -> !`TOption % aux ctx ty
    | TArrow (tl, ty) ->
      !`TArrow % List.fold_left (fun acc ty -> acc % aux ctx ty) (aux ctx ty) tl
    | TArray ty -> !`TArray % aux ctx ty
    | TDefault ty -> !`TDefault % aux ctx ty
    | TVar tv ->
      (* TVar.hash is not stable across executions (note: this assumes that we don't
         handle variables with the same id but differing names) *)
      !`TVar % !(TVar.name tv)
    | TForAll (tv, ty) ->
      !`TForAll % !(TVar.name tv) % aux ctx ty
    | TClosureEnv -> !`TClosureEnv
    | TError -> !`TError
  in
  aux () ty

let is_arrow ty = match unquantify ty with TArrow _, _ -> true | _ -> false

let rec has_arrow decl_ctx (ty : t) =
  match Mark.remove ty with
  | TArrow _ -> true
  | TLit _ -> false
  | TVar _ | TForAll _ | TClosureEnv | TError -> invalid_arg "Type.has_arrow"
  | TTuple tl -> List.exists (has_arrow decl_ctx) tl
  | TStruct n ->
    StructField.Map.exists
      (fun _ -> has_arrow decl_ctx)
      (StructName.Map.find n decl_ctx.ctx_structs)
  | TEnum n ->
    EnumConstructor.Map.exists
      (fun _ -> has_arrow decl_ctx)
      (EnumName.Map.find n decl_ctx.ctx_enums)
  | TAbstract _ -> false (* TODO: explicit what this means in this context *)
  | TOption ty | TArray ty | TDefault ty -> has_arrow decl_ctx ty

let rec arrow_return = function TArrow (_, b), _ -> arrow_return b | t -> t

let rec fully_known (ty : t) =
  match Mark.remove ty with
  | TArrow (targs, tret) -> List.for_all fully_known targs && fully_known tret
  | TLit _ -> true
  | TForAll _ ->
    TVar.Set.is_empty (free_vars ty) &&
    (match unquantify ty with TArrow _, _ -> true
                            | _ -> false)
  | TVar _ -> false
  | TClosureEnv -> true
  | TTuple tl -> List.for_all fully_known tl
  | TStruct _ -> true
  | TEnum _ -> true
  | TAbstract _ -> true
  | TOption ty | TArray ty | TDefault ty -> fully_known ty
  | TError -> true

module Map = Map.Make (struct
  type nonrec t = t

  let compare = compare
  let format = format
end)

let lookup_external tid =
  Catala_runtime.lookup_type
    ( Uid.Module.to_string
        (Option.get (Uid.Path.last_member (AbstractType.path tid))),
      AbstractType.base tid )

let lookup_external_handling tid =
  let module E = (val lookup_external tid) in
  match E.rtype with
  | External m -> (m :> (module Catala_runtime.Value.External))
  | _ -> assert false
