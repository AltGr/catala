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
open Shared_ast
module D = Dcalc.Ast
module A = Ast

let translate_var : 'm D.expr Var.t -> 'm A.expr Var.t = Var.translate

type 'm ex_tree =
  | Node of {
      tjust : 'm A.expr Var.t;
      tcons : 'm A.expr boxed;
      tchilds : 'm ex_tree list;
    }

let match_option ~some ~none e m =
  let pos = Expr.mark_pos m in
  Expr.ematch e Expr.option_enum
    (EnumConstructor.Map.of_seq
    @@ List.to_seq
         [
           ( Expr.none_constr,
             Expr.make_abs [| Var.make "_" |] none [TLit TUnit, pos] pos );
           ( Expr.some_constr,
             let v = Var.make "some" in
             Expr.make_abs [| v |] (some (Expr.evar v m)) [TAny, pos] pos );
         ])
    m

let rec translate_default ~to_option e =
  let pos = Expr.pos e in
  let m = Expr.mark_tany (Mark.get e) in
  let tbool = TLit TBool, pos in
  let mbool = Expr.with_ty m tbool in
  let rec mktree defs = function
    | ( EDefault
          {
            excepts = [];
            just = ELit (LBool true), _;
            cons = (EDefault _, _) as e;
          },
        _ ) ->
      mktree defs e
    | EDefault { excepts; just; cons }, _ ->
      let just = translate_expr just in
      let tcons =
        match Mark.remove cons with
        | EEmptyError ->
          if to_option then
            Expr.einj (Expr.elit LUnit m) Expr.none_constr Expr.option_enum m
          else Expr.eraise NoValueProvided m
        | _ -> translate_expr cons
      in
      let tcons =
        if to_option then Expr.einj tcons Expr.some_constr Expr.option_enum m
        else tcons
      in
      let vjust = Var.make "exc_condition" in
      let defs, tchilds = List.fold_left_map mktree defs excepts in
      (vjust, just, TLit TBool) :: defs, Node { tjust = vjust; tcons; tchilds }
    | (EApp _, _) as eapp ->
      (* The encoding of 'context' variables uses functions returning an option
         directly as exceptions *)
      let eapp = translate_expr eapp in
      let vdef = Var.make "opt_arg" in
      let vjust = Var.make "exc_condition" in
      let just =
        match_option (Expr.evar vdef m)
          ~none:(Expr.box (ELit (LBool false), m))
          ~some:(fun _ -> Expr.box (ELit (LBool true), m))
          mbool
      in
      let tcons =
        (* == Option.get *)
        match_option (Expr.evar vdef m)
          ~none:(Expr.eraise NoValueProvided m (* unreachable *))
          ~some:(fun v -> v)
          m
      in
      ( (vdef, eapp, TAny (* Option (TAny, pos) *))
        :: (vjust, just, TLit TBool)
        :: defs,
        Node { tjust = vjust; tcons; tchilds = [] } )
    | e ->
      Message.raise_spanned_error (Expr.pos e)
        "Exception that is not a default term: %a" Expr.format e
  in
  let rdefs, tree = mktree [] e in
  let defs = List.rev rdefs in
  let rec justs acc = function
    | Node { tjust; tchilds; _ } -> tjust :: List.fold_left justs acc tchilds
  in
  let mk_or = function
    | [] -> Expr.elit (LBool false) mbool
    | x :: xs ->
      List.fold_right
        (fun x e ->
          Expr.make_app
            (Expr.eop Or [TLit TBool, pos; TLit TBool, pos] m)
            [x; e] pos)
        xs x
  in
  let mk_vars_or vs = mk_or (List.map (fun v -> Expr.evar v mbool) vs) in
  let rec tree_to_ifthen_list conflict_conditions = function
    | Node { tjust; tcons; tchilds } ->
      let defs, chld_conditions =
        List.fold_left
          (fun (defs, chld_conds) node ->
            match justs [] node with
            | [v] -> defs, (node, v) :: chld_conds
            | vs ->
              let v = Var.make "exc_branch" in
              ( (v, mk_vars_or (List.rev vs), TLit TBool) :: defs,
                (node, v) :: chld_conds ))
          ([], []) tchilds
      in
      let rec descend chlds_conds =
        match chlds_conds with
        | [] -> [], []
        | (chld, _cond) :: rest ->
          let conds =
            List.fold_left (fun acc (_, v) -> v :: acc) conflict_conditions rest
          in
          let defs, chld_ifthen_list = tree_to_ifthen_list conds chld in
          let defs2, rest = descend rest in
          defs @ defs2, rest @ chld_ifthen_list
      in
      let defs2, rest = descend chld_conditions in
      ( defs2 @ defs,
        ( tjust,
          if conflict_conditions = [] then tcons
          else
            Expr.eifthenelse
              (mk_vars_or conflict_conditions)
              (Expr.eraise ConflictError m)
              tcons m )
        :: rest )
  in
  let defs2, ifthens = tree_to_ifthen_list [] tree in
  let body =
    List.fold_left
      (fun e (just, cons) -> Expr.eifthenelse (Expr.evar just mbool) cons e m)
      (if to_option then
       Expr.einj (Expr.elit LUnit m) Expr.none_constr Expr.option_enum m
      else Expr.eraise NoValueProvided m)
      ifthens
  in
  List.fold_left
    (fun e (var, def, ty) -> Expr.make_let_in var (ty, pos) def e pos)
    body (defs2 @ defs)

and translate_expr (e : 'm D.expr) : 'm A.expr boxed =
  let m = Mark.get e in
  match Mark.remove e with
  | EAbs { binder; tys } ->
    let vars, body = Bindlib.unmbind binder in
    let body =
      match body with
      | (EDefault _, _) as e ->
        (* A raw default term only appears as the body of functions that are
           supplied to scope context variables *)
        translate_default ~to_option:true e
      | e -> translate_expr e
    in
    let binder = Expr.bind (Array.map Var.translate vars) body in
    Expr.eabs binder tys m
  | EDefault _ ->
    (* A normal default term that is a fatal error if unresolved *)
    translate_default ~to_option:false e
  | EErrorOnEmpty e -> translate_expr e
  | EEmptyError ->
    (* This should only happen for unspecified context variables *)
    Expr.einj (Expr.elit LUnit m) Expr.none_constr Expr.option_enum
      (Expr.mark_tany m)
  | EOp { op; tys } -> Expr.eop (Operator.translate op) tys m
  | ( ELit _ | EApp _ | EArray _ | EVar _ | EExternal _ | EIfThenElse _
    | ETuple _ | ETupleAccess _ | EInj _ | EAssert _ | EStruct _
    | EStructAccess _ | EMatch _ ) as e ->
    Expr.map ~f:translate_expr (Mark.add m e)
  | _ -> .

let translate_program (prg : 'm D.program) : 'm A.program =
  let prg =
    {
      prg with
      decl_ctx =
        {
          prg.decl_ctx with
          ctx_enums =
            prg.decl_ctx.ctx_enums
            |> EnumName.Map.add Expr.option_enum Expr.option_enum_config;
        };
    }
  in
  Bindlib.unbox (Program.map_exprs ~f:translate_expr ~varf:translate_var prg)
