(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2023 Inria, contributor:
   Louis Gesbert <louis.gesbert@inria.fr>.

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

(* -- Definition of the lazy interpreter -- *)

let log fmt = Format.ifprintf Format.err_formatter (fmt ^^ "@\n")
let error e = Message.raise_spanned_error (Expr.pos e)
let noassert = true

module Env = struct
  type t = Env of (expr, elt) Var.Map.t
  and elt = { base : expr * t; mutable reduced : expr * t }
  and expr = (dcalc, annot custom) gexpr
  and annot = {conditions: (expr * t) list}

  let find v (Env t) = Var.Map.find v t

  (* let get_bas v t = let v, env = find v t in v, !env *)
  let add v e e_env (Env t) =
    Env (Var.Map.add v { base = e, e_env; reduced = e, e_env } t)

  let empty = Env Var.Map.empty

  let join (Env t1) (Env t2) =
    Env
      (Var.Map.union
         (fun _ x1 x2 ->
           (* assert (x1 == x2); *)
           Some x2)
         t1 t2)

  let print ppf (Env t) =
    Format.pp_print_list ~pp_sep:Format.pp_print_space
      (fun ppf (v, _) -> Print.var_debug ppf v)
      ppf (Var.Map.bindings t)
end

type expr = Env.expr
type annot = Env.annot = {conditions: (expr * Env.t) list}

type laziness_level = {
  eval_struct : bool;
      (* if true, evaluate members of structures, tuples, etc. *)
  eval_op : bool;
      (* if false, evaluate the operands but keep e.g. `3 + 4` as is *)
  eval_match : bool;
  eval_default : bool;
  (* if false, stop evaluating as soon as you can discriminate with
     `EEmptyError` *)
  eval_vars : expr Var.t -> bool;
      (* if false, variables are only resolved when they point to another
         unchanged variable *)
}

let value_level =
  {
    eval_struct = false;
    eval_op = true;
    eval_match = true;
    eval_default = true;
    eval_vars = (fun _ -> true);
  }

let add_condition ~condition e =
  Mark.map_mark
    (fun (Custom { pos; custom = { conditions } }) ->
       Custom {pos; custom = { conditions = condition::conditions } })
    e

let add_conditions ~conditions e =
  Mark.map_mark
    (fun (Custom { pos; custom = { conditions = c } }) ->
       Custom {pos; custom = { conditions = conditions@c } })
    e

let neg_op = function
  | Op.Xor -> Some Op.Eq
  | Op.Lt_int_int -> Some Op.Gte_int_int
  | Op.Lt_rat_rat -> Some Op.Gte_rat_rat
  | Op.Lt_mon_mon -> Some Op.Gte_mon_mon
  | Op.Lt_dat_dat -> Some Op.Gte_dat_dat
  | Op.Lt_dur_dur -> Some Op.Gte_dur_dur
  | Op.Lte_int_int -> Some Op.Gt_int_int
  | Op.Lte_rat_rat -> Some Op.Gt_rat_rat
  | Op.Lte_mon_mon -> Some Op.Gt_mon_mon
  | Op.Lte_dat_dat -> Some Op.Gt_dat_dat
  | Op.Lte_dur_dur -> Some Op.Gt_dur_dur
  | Op.Gt_int_int -> Some Op.Lte_int_int
  | Op.Gt_rat_rat -> Some Op.Lte_rat_rat
  | Op.Gt_mon_mon -> Some Op.Lte_mon_mon
  | Op.Gt_dat_dat -> Some Op.Lte_dat_dat
  | Op.Gt_dur_dur -> Some Op.Lte_dur_dur
  | Op.Gte_int_int -> Some Op.Lt_int_int
  | Op.Gte_rat_rat -> Some Op.Lt_rat_rat
  | Op.Gte_mon_mon -> Some Op.Lt_mon_mon
  | Op.Gte_dat_dat -> Some Op.Lt_dat_dat
  | Op.Gte_dur_dur -> Some Op.Lt_dur_dur
  | _ -> None

let rec bool_negation e =
  match Expr.skip_wrappers e with
  | ELit (LBool true), m -> ELit (LBool false), m
  | ELit (LBool false), m -> ELit (LBool true), m
  | EApp {f = EOp { op = Op.Not; _ }, _; args = [e, _]}, m -> e, m
  | EApp {f = EOp { op; tys }, mop; args = [e1; e2]}, m as e ->
    (match op with
     | Op.And -> EApp {f = EOp { op = Op.Or; tys }, mop; args = [bool_negation e1; bool_negation e2]}, m
     | Op.Or -> EApp {f = EOp { op = Op.And; tys }, mop; args = [bool_negation e1; bool_negation e2]}, m
     | op -> match neg_op op with
       | Some op ->
         EApp {f = EOp { op; tys }, mop; args = [e1; e2]}, m
       | None ->
         EApp {f = EOp {op=Op.Not; tys=[TLit TBool, Expr.mark_pos m]}, m; args = [e]}, m)
  | (_, m) as e ->
    EApp {f = EOp {op=Op.Not; tys=[TLit TBool, Expr.mark_pos m]}, m; args = [e]}, m

let rec lazy_eval : decl_ctx -> Env.t -> laziness_level -> expr -> expr * Env.t =
 fun ctx env llevel e0 ->
  let eval_to_value ?(eval_default = true) env e =
    lazy_eval ctx env { value_level with eval_default } e
  in
  match e0 with
  | EVar v, _ ->
    if (not llevel.eval_default) || not (llevel.eval_vars v) then e0, env
    else
      (* Variables reducing to EEmpty should not propagate to parent EDefault
         (?) *)
      let env_elt =
        try Env.find v env
        with Not_found ->
          error e0 "Variable %a undefined [@[<hv>%a@]]" Print.var_debug v
            Env.print env
      in
      let e, env1 = env_elt.reduced in
      let r, env1 = lazy_eval ctx env1 llevel e in
      env_elt.reduced <- r, env1;
      r, Env.join env env1
  | EApp { f; args }, m -> (
    if
      (not llevel.eval_default)
      && not (List.equal Expr.equal args [ELit LUnit, m])
      (* Applications to () encode thunked default terms *)
    then e0, env
    else
      match eval_to_value env f with
      | (EAbs { binder; _ }, _), env ->
        let vars, body = Bindlib.unmbind binder in
        log "@[<v 2>@[<hov 4>{";
        let env =
          Seq.fold_left2
            (fun env1 var e ->
              log "@[<hov 2>LET %a = %a@]@ " Print.var_debug var Expr.format e;
              Env.add var e env env1)
            env (Array.to_seq vars) (List.to_seq args)
        in
        log "@]@[<hov 4>IN [%a]@]" (Print.expr ~debug:true ()) body;
        let e, env = lazy_eval ctx env llevel body in
        log "@]}";
        e, env
      | ((EOp { op; _ }, m) as f), env ->
        let env, args =
          List.fold_left_map
            (fun env e ->
              let e, env = lazy_eval ctx env llevel e in
              env, e)
            env args
        in
        if not llevel.eval_op then (EApp { f; args }, m), env
        else
          let renv = ref env in
          (* Dirty workaround returning env and conds from evaluate_operator *)
          let eval e =
            let e, env = lazy_eval ctx !renv llevel e in
            renv := env;
            e
          in
          Interpreter.evaluate_operator eval op m args, !renv
      (* fixme: this forwards eempty *)
      | e, _ -> error e "Invalid apply on %a" Expr.format e)
  | (EAbs _ | ELit _ | EOp _ | EEmptyError), _ -> e0, env (* these are values *)
  | (EStruct _ | ETuple _ | EInj _ | EArray _), _ ->
    if not llevel.eval_struct then e0, env
    else
      let env, e =
        Expr.map_gather ~acc:env ~join:Env.join
          ~f:(fun e ->
            let e, env = lazy_eval ctx env llevel e in
            env, Expr.box e)
          e0
      in
      Expr.unbox e, env
  | EStructAccess { e; name; field }, _ -> (
    if not llevel.eval_default then e0, env
    else
      match eval_to_value env e with
      | (EStruct { name = n; fields }, _), env when StructName.equal name n ->
        let e, env = lazy_eval ctx env llevel (StructField.Map.find field fields) in
        e, env
      | e, _ -> error e "Invalid field access on %a" Expr.format e)
  | ETupleAccess { e; index; size }, _ -> (
    if not llevel.eval_default then e0, env
    else
      match eval_to_value env e with
      | (ETuple es, _), env when List.length es = size ->
        lazy_eval ctx env llevel (List.nth es index)
      | e, _ -> error e "Invalid tuple access on %a" Expr.format e)
  | EMatch { e; name; cases }, _ -> (
    if not llevel.eval_match then e0, env
    else
      match eval_to_value env e with
      | (EInj { name = n; cons; e }, m), env when EnumName.equal name n ->
        let condition = e, env in
        let e, env =
          lazy_eval ctx env llevel
            (EApp { f = EnumConstructor.Map.find cons cases; args = [e] }, m)
        in
        add_condition ~condition e, env
      | e, _ -> error e "Invalid match argument %a" Expr.format e)
  | EDefault { excepts; just; cons }, m -> (
    let excs =
      List.filter_map
        (fun e ->
          match eval_to_value env e ~eval_default:false with
          | (EEmptyError, _), _ -> None
          | e -> Some e)
        excepts
    in
    match excs with
    | [] -> (
      match eval_to_value env just with
      | (ELit (LBool true), _), _ ->
        let condition = just, env in
        let e, env = lazy_eval ctx env llevel cons in
        add_condition ~condition e, env
      | (ELit (LBool false), _), _ -> (EEmptyError, m), env
      (* Note: conditions for empty are skipped *)
      | e, _ -> error e "Invalid exception justification %a" Expr.format e)
    | [(e, env)] ->
      log "@[<hov 5>EVAL %a@]" Expr.format e;
      lazy_eval ctx env llevel e
    | _ :: _ :: _ ->
      Message.raise_multispanned_error
        ((None, Expr.mark_pos m)
        :: List.map (fun (e, _) -> None, Expr.pos e) excs)
        "Conflicting exceptions")
  | EIfThenElse { cond; etrue; efalse }, _ -> (
    match eval_to_value env cond with
    | (ELit (LBool true), _), _ ->
      let condition = cond, env in
      let e, env = lazy_eval ctx env llevel etrue in
      add_condition ~condition e, env
    | (ELit (LBool false), m), _ ->
      let condition = bool_negation cond, env in
      let e, env = lazy_eval ctx env llevel efalse in
      (match efalse with
       (* The negated condition is not added for nested [else if] to reduce verbosity *)
       | EIfThenElse _, _ -> e, env
       | _ -> add_condition ~condition e, env)
    | e, _ -> error e "Invalid condition %a" Expr.format e)
  | EErrorOnEmpty e, _ -> (
    match eval_to_value env e ~eval_default:false with
    | ((EEmptyError, _) as e'), _ ->
      (* This does _not_ match the eager semantics ! *)
      error e' "This value is undefined %a" Expr.format e
    | e, env -> lazy_eval ctx env llevel e)
  | EAssert e, m -> (
    if noassert then (ELit LUnit, m), env
    else
      match eval_to_value env e with
      | (ELit (LBool true), m), env -> (ELit LUnit, m), env
      | (ELit (LBool false), _), _ ->
        error e "Assert failure (%a)" Expr.format e error e "Assert failure (%a)"
          Expr.format e
      | _ -> error e "Invalid assertion condition %a" Expr.format e)
  | EExternal _, _ -> assert false (* todo *)
  | _ -> .

let result_level base_vars =
  {
    value_level with
    eval_struct = true;
    eval_op = false;
    eval_vars = (fun v -> not (Var.Set.mem v base_vars));
  }

let interpret_program (prg : ('dcalc, 'm) gexpr program)
    (scope : ScopeName.t) : ('t, 'm) gexpr * Env.t =
  let ctx = prg.decl_ctx in
  let all_env, scopes =
    Scope.fold_left prg.code_items ~init:(Env.empty, ScopeName.Map.empty)
      ~f:(fun (env, scopes) item v ->
        match item with
        | ScopeDef (name, body) ->
          let e = Scope.to_expr ctx body (Scope.get_body_mark body) in
          let e = Expr.remove_logging_calls (Expr.unbox e) in
          ( Env.add v (Expr.unbox e) env env,
            ScopeName.Map.add name (v, body.scope_body_input_struct) scopes )
        | Topdef (_, _, e) -> Env.add v e env env, scopes)
  in
  let scope_v, _scope_arg_struct = ScopeName.Map.find scope scopes in
  let e, env = (Env.find scope_v all_env).base in
  log "=====================";
  log "%a" (Print.expr ~debug:true ()) e;
  log "=====================";
  (* let m = Mark.get e in *)
  (* let application_arg =
   *   Expr.estruct scope_arg_struct
   *     (StructField.Map.map
   *        (function
   *          | TArrow (ty_in, ty_out), _ ->
   *            Expr.make_abs
   *              [| Var.make "_" |]
   *              (Bindlib.box EEmptyError, Expr.with_ty m ty_out)
   *              ty_in (Expr.mark_pos m)
   *          | ty -> Expr.evar (Var.make "undefined_input") (Expr.with_ty m ty))
   *        (StructName.Map.find scope_arg_struct ctx.ctx_structs))
   *     m
   * in *)
  match e with
  | EAbs { binder; _ }, _ ->
    let _vars, e = Bindlib.unmbind binder in
    let rec get_vars base_vars env = function
      | EApp { f = EAbs { binder; _ }, _; args = [arg] }, _ ->
        let vars, e = Bindlib.unmbind binder in
        let var = vars.(0) in
        let base_vars =
          match Expr.skip_wrappers arg with
          | ELit _, _ -> Var.Set.add var base_vars
          | _ -> base_vars
        in
        let env = Env.add var arg env env in
        get_vars base_vars env e
      | e -> base_vars, env, e
    in
    let base_vars, env, e = get_vars Var.Set.empty env e in
    lazy_eval ctx env (result_level base_vars) e
  | _ -> assert false

let print_value_with_env ctx ppf env expr =
  let already_printed = ref Var.Set.empty in
  let rec aux env ppf expr =
    Print.expr ~debug:true () ppf expr;
    Format.pp_print_cut ppf ();
    let vars = Var.Set.diff (Expr.free_vars expr) !already_printed in
    Var.Set.iter
      (fun v ->
        let e, env = (Env.find v env).reduced in
        let e, env = lazy_eval ctx env (result_level Var.Set.empty) e in
        Format.fprintf ppf "@[<hov 2>%a %a =@ %a =@ %a@]@,@," Print.punctuation
          "»" Print.var_debug v Expr.format
          (fst (lazy_eval ctx env value_level e))
          (aux env) e)
      vars;
    already_printed := Var.Set.union !already_printed vars;
    Format.pp_print_cut ppf ()
  in
  Format.pp_open_vbox ppf 2;
  aux env ppf expr;
  Format.pp_close_box ppf ()

module V = struct
  type t = expr

  let compare a b = Expr.compare a b

  let hash = function
    | EVar v, _ -> Var.hash v
    | EAbs { tys; _ }, _ -> Hashtbl.hash tys
    | e, _ -> Hashtbl.hash e

  let equal a b = Expr.equal a b
end

module E = struct
  type hand_side = Lhs of string | Rhs of string
  type t = { side: hand_side option; condition: bool }

  let compare x y =
    match Bool.compare x.condition y.condition with
    | 0 ->
      Option.compare (fun x y ->
          match x, y with
          | Lhs s, Lhs t | Rhs s, Rhs t -> String.compare s t
          | Lhs _, Rhs _ -> -1
          | Rhs _, Lhs _ -> 1)
        x.side y.side
    | n -> n

  let default = { side = None; condition = false }
end

module G = Graph.Persistent.Digraph.AbstractLabeled (V) (E)

let op_kind = function
  | Op.Add_int_int | Add_rat_rat | Add_mon_mon | Add_dat_dur _ | Add_dur_dur
  | Sub_int_int | Sub_rat_rat | Sub_mon_mon | Sub_dat_dat | Sub_dat_dur
  | Sub_dur_dur ->
    `Sum
  | Mult_int_int | Mult_rat_rat | Mult_mon_rat | Mult_dur_int | Div_int_int
  | Div_rat_rat | Div_mon_rat | Div_mon_mon | Div_dur_dur ->
    `Product
  | Round_mon | Round_rat -> `Round
  | Map | Filter | Reduce | Fold -> `Fct
  | _ -> `Other

module GTopo = Graph.Topological.Make (G)

let to_graph ctx env expr =
  let rec aux env g e =
    (* lazy_eval ctx env (result_level base_vars) e *)
    match Expr.skip_wrappers e with
    | ( EApp
          {
            f = EOp { op = ToRat_int | ToRat_mon | ToMoney_rat; _ }, _;
            args = [arg];
          },
        _ ) ->
      aux env g arg
    (* we skip conversions *)
    | ELit l, _ ->
      let v = G.V.create e in
      G.add_vertex g v, v
    | (EVar var, _) as e ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let child, env = (Env.find var env).base in
      let g, child_v = aux env g child in
      G.add_edge g v child_v, v
    | EApp { f = EOp { op = _; _ }, _; args }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let g, children = List.fold_left_map (aux env) g args in
      List.fold_left (fun g -> G.add_edge g v) g children, v
    | EInj { e; _ }, _ -> aux env g e
    | EStruct { fields; _ }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let args = List.map snd (StructField.Map.bindings fields) in
      let g, children = List.fold_left_map (aux env) g args in
      List.fold_left (fun g -> G.add_edge g v) g children, v
    | _ ->
      Format.eprintf "%a" Expr.format e;
      assert false
  in
  let base_g, _ = aux env G.empty expr in
  base_g

let rec is_const e =
  match Expr.skip_wrappers e with
  | ELit _, _ -> true
  | EInj { e; _ }, _ -> is_const e
  | EStruct { fields; _ }, _ ->
    StructField.Map.for_all (fun _ e -> is_const e) fields
  | EArray el, _ -> List.for_all is_const el
  | _ -> false

let program_to_graph
    (prg : (dcalc, 'm) gexpr program)
    (scope : ScopeName.t) : G.t * expr Var.Set.t * Env.t =
  let ctx = prg.decl_ctx in
  let customize =
    Expr.map_marks
      ~f:(fun m -> Custom {
          pos = Expr.mark_pos m;
          custom = { conditions = [] }
        })
  in
  let all_env, scopes =
    Scope.fold_left prg.code_items ~init:(Env.empty, ScopeName.Map.empty)
      ~f:(fun (env, scopes) item v ->
        match item with
        | ScopeDef (name, body) ->
          let e = Scope.to_expr ctx body (Scope.get_body_mark body) in
          let e = customize (Expr.unbox e) in
          let e = Expr.remove_logging_calls (Expr.unbox e) in
          ( Env.add (Var.translate v) (Expr.unbox e) env env,
            ScopeName.Map.add name (v, body.scope_body_input_struct) scopes )
        | Topdef (_, _, e) -> Env.add (Var.translate v) (Expr.unbox (customize e)) env env, scopes)
  in
  let scope_v, _scope_arg_struct = ScopeName.Map.find scope scopes in
  let e, env = (Env.find (Var.translate scope_v) all_env).base in
  let e =
    match e with
    | EAbs { binder; _ }, _ ->
      let _vars, e = Bindlib.unmbind binder in
      e
    | _ -> assert false
  in
  let rec get_vars base_vars env = function
    | EApp { f = EAbs { binder; _ }, _; args = [arg] }, _ ->
      let vars, e = Bindlib.unmbind binder in
      let var = vars.(0) in
      let base_vars =
        if is_const arg then Var.Set.add var base_vars else base_vars
      in
      let env = Env.add var arg env env in
      get_vars base_vars env e
    | e -> base_vars, env, e
  in
  let base_vars, env, e = get_vars Var.Set.empty env e in
  let e1, env = lazy_eval ctx env (result_level base_vars) e in
  let level =
    {
      value_level with
      eval_struct = true;
      eval_op = false;
      eval_match = false;
      eval_vars = (fun v -> false);
    }
  in
  let rec aux parent (g, var_vertices, env0) e =
    let e, env0 = lazy_eval ctx env0 level e in
    let m = Mark.get e in
    let Custom { custom = { conditions; _ }; _ } = m in
    let g, var_vertices, env0 =
      match parent with
      | None -> g, var_vertices, env0
      | Some parent ->
        List.fold_left (fun (g, var_vertices, env0) (econd, env) ->
            let (g, var_vertices, env), vcond = aux (Some parent) (g, var_vertices, env) econd in
            G.add_edge_e g (G.E.create parent { side = None; condition = true } vcond),
            var_vertices,
            Env.join env0 env)
          (g, var_vertices, env0) conditions
    in
    let e = Mark.set m (Expr.skip_wrappers e) in
    match e with
    | ( EApp
          {
            f = EOp { op = ToRat_int | ToRat_mon | ToMoney_rat; _ }, _;
            args = [arg];
          },
        _ ) ->
      aux parent (g, var_vertices, env0) (Mark.set m arg)
    (* we skip conversions *)
    | ELit l, _ ->
      let v = G.V.create e in
      (G.add_vertex g v, var_vertices, env0), v
    | (EVar var, _) -> (
      try (g, var_vertices, env0), Var.Map.find var var_vertices
      with Not_found -> (
        let v = G.V.create e in
        let g = G.add_vertex g v in
        try
          let child, env = (Env.find var env0).base in
          let (g, var_vertices, env), child_v =
            aux (Some v) (g, var_vertices, Env.join env0 env) child
          in
          let var_vertices =
            (* Duplicates non-base constant var nodes *)
            if Var.Set.mem var base_vars then var_vertices
            else
              let rec is_lit v =
                match G.V.label v with
                | ELit _, _ -> true
                | EVar var, _ when not (Var.Set.mem var base_vars) -> (
                  match G.succ g v with [v] -> is_lit v | _ -> false)
                | _ -> false
              in
              if is_lit child_v then var_vertices
            (* This duplicates constant var nodes *)
              else Var.Map.add var v var_vertices
          in
          (G.add_edge g v child_v, var_vertices, env), v
        with Not_found -> (g, var_vertices, env), v))
    | ( EApp
          {
            f = EOp { op = Map | Filter | Reduce | Fold; _ }, _;
            args = _ :: args;
          },
        _ ) ->
      (* First argument (which is a function) is ignored *)
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), children =
        List.fold_left_map (aux (Some v)) (g, var_vertices, env0) args
      in
      ( (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env),
        v )
    | EApp { f = EOp { op; _ }, _; args = [lhs; rhs] }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), lhs = aux (Some v) (g, var_vertices, env0) lhs in
      let (g, var_vertices, env), rhs = aux (Some v) (g, var_vertices, env) rhs in
      let lhs_label, rhs_label =
        match op with
        | Add_int_int | Add_rat_rat | Add_mon_mon | Add_dat_dur _ | Add_dur_dur
          ->
          Some (E.Lhs "⊕"), Some (E.Rhs "⊕")
        | Sub_int_int | Sub_rat_rat | Sub_mon_mon | Sub_dat_dat | Sub_dat_dur
        | Sub_dur_dur ->
          Some (E.Lhs "⊕"), Some (E.Rhs "⊖")
        | Mult_int_int | Mult_rat_rat | Mult_mon_rat | Mult_dur_int ->
          Some (E.Lhs "⊗"), Some (E.Rhs "⊗")
        | Div_int_int | Div_rat_rat | Div_mon_rat | Div_mon_mon | Div_dur_dur ->
          Some (E.Lhs "⊗"), Some (E.Rhs "⊘")
        | _ -> None, None
      in
      let g = G.add_edge_e g (G.E.create v { side = lhs_label; condition = false } lhs) in
      let g = G.add_edge_e g (G.E.create v { side = rhs_label; condition = false } rhs) in
      (g, var_vertices, env), v
    | EApp { f = EOp { op = _; _ }, _; args }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), children =
        List.fold_left_map (aux (Some v)) (g, var_vertices, env0) args
      in
      ( (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env),
        v )
    | EInj { e; _ }, _ -> aux parent (g, var_vertices, env0) e
    | EStruct { fields; _ }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let args = List.map snd (StructField.Map.bindings fields) in
      let (g, var_vertices, env), children =
        List.fold_left_map (aux (Some v)) (g, var_vertices, env0) args
      in
      ( (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env),
        v )
    | EArray elts, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), children =
        List.fold_left_map (aux (Some v)) (g, var_vertices, env0) elts
      in
      ( (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env),
        v )
    | EAbs _, _ ->
      (g, var_vertices, env), G.V.create e (* (testing -> ignored) *)
    | EMatch {name; e; cases}, _ ->
      aux parent (g, var_vertices, env0) e
    | _ ->
      Format.eprintf "%a" Expr.format e;
      assert false
  in
  let (g, vmap, env), _ = aux None (G.empty, Var.Map.empty, env) e in
  (* Add conditions ! *)
  (* let (g, vmap, env) =
   *   G.fold_vertex (fun v (g, vmap, env) ->
   *     let e = G.V.label v in
   *     let Custom { custom = { conditions; _ }; _ } = Mark.get e in
   *     List.fold_left (fun (g, vmap, env0) (econd, env) ->
   *         let (g, vmap, env), vcond = aux (g, vmap, env) econd in
   *         G.add_edge_e g (G.E.create v { side = None; condition = true } vcond),
   *         vmap,
   *         Env.join env0 env)
   *       (g, vmap, env) conditions)
   *     g
   *     (g, vmap, env)
   * in *)
  log "BASE: @[<v>%a@]"
    (Format.pp_print_list Print.var)
    (Var.Set.elements base_vars);
  g, base_vars, env

(* let rec graph_cleanup g v =
 *   let rec aux g parents v =
 *     let chld = G.succ g v in
 *     List.fold_left 
 *     match parents with
 *     | [] ->
 *       let chld = G.succ g v in
 *       let g = G.fold_succ_e v in
 *     let g', chld = List.fold_left_map graph_cleanup g (G.succ g v) in
 *     let g' = List.fold_left (G.add_edge g' v) g' chld in
 *     g', v
 * 
 * 
 *   
 *   match List.map G.V.label (G.pred g v), G.V.label v with
 *   | [], _ ->
 *     let chld = G.succ g v in
 *     let g = G.remove_edge g v in
 *     let g', chld = List.fold_left_map graph_cleanup g (G.succ g v) in
 *     let g' = List.fold_left (G.add_edge g' v) g' chld in
 *     g', v
 *   | [EVar _, _ as chld], (EVar _, _) ->
 *     let out_e = G.succ_e g' v
 *     let (g', chld) = graph_cleanup g' g chld
 *     G.add_vertex g' v
 * 
 *   | (EVar _, _) as e, [EVar _, _ as chld] ->
 *     let (g', chld) = graph_cleanup g' g chld
 *     G.add_vertex g' v *)

let reverse_graph g =
  G.fold_edges_e
    (fun e g ->
      G.add_edge_e (G.remove_edge_e g e)
        (G.E.create (G.E.dst e) (G.E.label e) (G.E.src e)))
    g g

let subst_by v1 v2 e =
  let rec f = function
    | EVar v, m when Var.equal v v1 -> Expr.box (EVar v2, m)
    | e -> Expr.map ~f e
  in
  Expr.unbox (f e)

let map_vertices f g =
  G.fold_vertex
    (fun v g ->
      let v' = G.V.create (f (G.V.label v)) in
      let g =
        G.fold_pred_e
          (fun e g -> G.add_edge_e g (G.E.create (G.E.src e) (G.E.label e) v'))
          g v g
      in
      let g =
        G.fold_succ_e
          (fun e g -> G.add_edge_e g (G.E.create v' (G.E.label e) (G.E.dst e)))
          g v g
      in
      G.remove_vertex g v)
    g g

let rec graph_cleanup g =
  (* let _g =
   *   let module GCtr = Graph.Contraction.Make (G) in
   *   GCtr.contract
   *     (fun e ->
   *       G.E.label e = None
   *       &&
   *       match G.V.label (G.E.src e), G.V.label (G.E.dst e) with
   *       | (EVar _, _), (EVar _, _) -> true
   *       | ( (EApp { f = EOp { op = op1; _ }, _; args = [_; _] }, _),
   *           (EApp { f = EOp { op = op2; _ }, _; args = [_; _] }, _) ) -> (
   *         match op_kind op1, op_kind op2 with
   *         | `Sum, `Sum -> true
   *         | `Prod, `Prod -> true
   *         | _ -> false)
   *       | _ -> false)
   *     g
   * in *)
  let module GTop = Graph.Topological.Make (G) in
  let g, substs =
    (* Remove intermediate variables *)
    GTop.fold (* Result -> variables order *)
      (fun v (g, substs) ->
        let succ_e = G.succ_e g v in
        if List.exists (fun ed -> (G.E.label ed).condition) succ_e then g, substs else
        let succ = List.map G.E.dst succ_e in
        match G.V.label v, succ, List.map G.V.label succ with
        | (EVar var1, m1), [v2], [(EVar var2, m2)] ->
          let g =
            List.fold_left
              (fun g e ->
                G.add_edge_e g (G.E.create (G.E.src e) (G.E.label e) v2))
              g (G.pred_e g v)
          in
          G.remove_vertex g v, fun e -> subst_by var1 var2 (substs e)
        | _ -> g, substs)
      g (g, Fun.id)
  in
  let g = map_vertices substs g in
  let g =
    (* Merge intermediate operations *)
    let g = reverse_graph g in
    GTop.fold (* Variables -> result order *)
      (fun v g ->
        let succ = G.succ g v in
        match G.V.label v, succ, List.map G.V.label succ with
        | (EApp { f = EOp _, _; _ }, _), [v2], [(EApp { f = EOp _, _; _ }, _)]
          ->
          let g =
            List.fold_left
              (fun g e ->
                G.add_edge_e g (G.E.create (G.E.src e) (G.E.label e) v2))
              g (G.pred_e g v)
          in
          G.remove_vertex g v
        | _ -> g)
      g g
    |> reverse_graph
  in
  let g =
    (* Remove separate nodes for variable literal values *)
    G.fold_vertex
      (fun v g ->
        match G.V.label v, List.map G.V.label (G.pred g v) with
        (* | (ELit _, _), [EVar _, _] -> G.remove_vertex g v *)
        | (ELit _, _), _ ->
          G.remove_vertex g v (* <- test with print full form. *)
        | _, _ -> g)
      g g
  in
  (* let g =
   *   G.fold_edges_e (fun e g ->
   *       match G.V.label (G.E.src e) with
   *       | EApp { f = EOp { op = op1 }, _; args = [_; _] }, _ ->
   *
   *
   *       | (ELit _, _), [EVar _, _] -> G.remove_vertex g v
   *       | _, _ -> g)
   *     g g
   * in *)
  g

(* let simplif_op: type a. a Op.t -> 'b = function
 *   | Op.ToRat_int
 *   | ToRat_mon -> Op.ToRat
 *   | ToMoney_rat -> ToMoney
 *   | Round_rat
 *   | Round_mon -> Round
 *   | Minus_int
 *   | Minus_rat
 *   | Minus_mon
 *   | Minus_dur -> Minus
 *   | Add_int_int
 *   | Add_rat_rat
 *   | Add_mon_mon
 *   | Add_dat_dur _
 *   | Add_dur_dur -> Add
 *   | Sub_int_int
 *   | Sub_rat_rat
 *   | Sub_mon_mon
 *   | Sub_dat_dat
 *   | Sub_dat_dur
 *   | Sub_dur_dur -> Sub
 *   | Mult_int_int
 *   | Mult_rat_rat
 *   | Mult_mon_rat
 *   | Mult_dur_int -> Mult
 *   | Div_int_int
 *   | Div_rat_rat
 *   | Div_mon_mon
 *   | Div_mon_rat
 *   | Div_dur_dur -> Div
 *   | Lt_int_int
 *   | Lt_rat_rat
 *   | Lt_mon_mon
 *   | Lt_dur_dur
 *   | Lt_dat_dat -> Lt
 *   | Lte_int_int
 *   | Lte_rat_rat
 *   | Lte_mon_mon
 *   | Lte_dur_dur
 *   | Lte_dat_dat -> Lte
 *   | Gt_int_int
 *   | Gt_rat_rat
 *   | Gt_mon_mon
 *   | Gt_dur_dur
 *   | Gt_dat_dat -> Gt
 *   | Gte_int_int
 *   | Gte_rat_rat
 *   | Gte_mon_mon
 *   | Gte_dur_dur
 *   | Gte_dat_dat -> Gte
 *   | Eq_int_int
 *   | Eq_rat_rat
 *   | Eq_mon_mon
 *   | Eq_dur_dur
 *   | Eq_dat_dat -> Eq
 *   | ( Not | GetDay | GetMonth | GetYear | FirstDayOfMonth | LastDayOfMonth | And
 *     | Or | Xor | HandleDefault | HandleDefaultOpt | Log _ | Length | Eq | Map
 *     | Concat | Filter | Reduce | Fold
 *     | Minus | ToRat | ToMoney | Round | Add | Sub | Mult | Div | Lt | Lte | Gt
 *     | Gte ) as op ->
 *     op
 * 
 * let rec simplif_ops:
 *   type a. (<overloaded: a; ..>, 't) gexpr -> (<overloaded: yes; ..>, 't) gexpr boxed
 *   =
 *   function
 *   | EOp { op; tys }, m ->
 *     Expr.box (EOp { op = simplif_op op; tys }, m)
 *   | (ELit _
 *   | EApp _
 *   | EArray _
 *   | EVar _
 *   | EAbs _
 *   | EIfThenElse _
 *   | ETuple _
 *   | ETupleAccess _
 *   | EInj _
 *   | EAssert _
 *   | EDefault _
 *   | EEmptyError
 *   | EErrorOnEmpty _
 *   | ECatch _
 *   | ERaise _
 *   | ELocation _
 *   | EStruct _
 *   | EDStructAccess _
 *   | EStructAccess _
 *   | EMatch _
 *   | EScopeCall _), _
 *     as e -> Expr.map ~f:simplif_ops e *)

let to_dot oc ctx env base_vars g =
  let module GPr = Graph.Graphviz.Dot (struct
    include G

    let graph_attributes _ =
      [
        (* `Rankdir `LeftToRight *)
      ]
    let default_vertex_attributes _ = []

    let vertex_label v =
      let e = Expr.skip_wrappers (G.V.label v) in
      match e with
      | EVar v, _ -> (
        match lazy_eval ctx env value_level e (* Env.find v env *) with
        | (ELit l, _), _ ->
          Format.asprintf "%s = %a" (Bindlib.name_of v) Print.lit l
        | _ -> Format.asprintf "%s" (Bindlib.name_of v)
        | exception Not_found -> Format.asprintf "YY %s" (Bindlib.name_of v))
      | (EApp { f = EOp { op; _ }, _; _ }, _) as e -> (
        match op_kind op with
         | `Sum | `Product | `Round -> Format.asprintf "%a" Expr.format e
        | `Fct -> Format.asprintf "<%a>" (Print.operator ~debug:false) op
        | `Other -> Format.asprintf "%a" Expr.format e)
      | EApp { f; _ }, _ -> Format.asprintf "%a" Expr.format f
      | ELit l, _ -> Format.asprintf "%a" Print.lit l
      | EStruct { name; _ }, _ ->
        Format.asprintf "{%a}" StructName.format_t name
      | EArray elts, _ ->
        Format.asprintf "[collection] (length=%d)" (List.length elts)
      | z -> Format.asprintf "[%a]" Expr.format z

    let vertex_name v = Printf.sprintf "x%03d" (G.V.hash v)

    let vertex_attributes v =
      let e = V.label v in
      let pos = Expr.pos e in
      let loc_text =
        Re.replace_string Re.(compile (char '\n')) ~by:"&#10;"
          (String.concat "\n» " (List.rev (Pos.get_law_info pos)) ^ "\n")
      in
      `Label (vertex_label v (* ^ "\n" ^ loc_text *))
      :: `Comment (loc_text)
      (* :: `Url ("https://catala-lang.org/en/examples/housing-benefits#" ^
       *          Re.(replace_string
       *                (compile (seq [char '/'; rep1 (diff any (char '/')); str "/../"]))
       *                ~by:"/"
       *                (Pos.get_file pos))
       *          ^ "-" ^ string_of_int (Pos.get_start_line pos)) *)
      :: `Url ("https://github.com/CatalaLang/catala/blob/master/" ^ Pos.get_file pos ^ "#L" ^ string_of_int (Pos.get_start_line pos))
      (* :: `Fontname "monospace" *)
      ::
      (match G.V.label v with
      | EVar var, _ -> (
        if Var.Set.mem var base_vars then
          [`Style `Filled; `Fillcolor 0xffaa55; `Shape `Box]
        else if List.exists (fun e -> not (G.E.label e).condition) (G.succ_e g v) then (* non-constants *)
          [`Style `Filled; `Fillcolor 0xffee99; `Shape `Box]
        else (* Constants *)
          [`Style `Filled; `Fillcolor 0x77aaff; `Shape `Note])
      | EApp { f = EOp { op; _ }, _; _ }, _ -> (
        match op_kind op with `Sum | `Product | _ -> [`Shape `Box] (* | _ -> [] *))
      | _ -> [])

    let get_subgraph v =
      match G.V.label v with
      | EVar var, _ -> (
        if Var.Set.mem var base_vars then
          Some
            {
              Graph.Graphviz.DotAttributes.sg_name = "inputs";
              sg_attributes = [];
              sg_parent = None;
            }
        else
          match List.map G.V.label (G.succ g v) with
          (* | [] | [ELit _, _] ->
           *   Some
           *     {
           *       Graph.Graphviz.DotAttributes.sg_name = "constants";
           *       sg_attributes = [`Shape `Box];
           *       sg_parent = None;
           *     } *)
          | _ -> None)
      | _ -> None

    let default_edge_attributes _ = []

    let edge_attributes e =
      match E.label e with
      | { condition = true; _ } -> [ `Style `Dashed; `Penwidth 5.; `Color 0xff7700 ]
      | { side = Some (Lhs s | Rhs s); _ } -> [ (* `Label s; `Color 0xbb7700 *) ]
      | _ -> []
  end) in
  GPr.output_graph oc (reverse_graph g)

(*  let g =
 *    (* Flatten multiplications and additions *)
 *    G.fold_edges_e (fun e g' ->
 *        let src = G.E.src e and dst = G.E.dst e in
 *        match G.V.label src, G.V.label dst with
 *        | (EApp { f = EOp { op =
 *                              (Sub
 *                              | Sub_int_int
 *                              | Sub_rat_rat
 *                              | Sub_mon_mon
 *                              | Sub_dat_dat
 *                              | Sub_dat_dur
 *                              | Sub_dur_dur) }
 * 
 * Plus, _; _ }, _; _}, _),
 *          (EApp { op = EOp { op = Minus, _; _ }, _; _}; _) ->
 *          G.add_edge_e (G.E.create src (Some "-") dst)
 *          G.remove_edge_e e
 *      )
 *      g
 *  in
 *  let rec flatten g v =
 *    
 *    let module GTra = Graph.Traverse.Bfs(G) in
 *    FTra.fold (fun v -> *)

(* module V = struct
 *   type t = { var: expr Var.t option; expr: expr; label: string }
 * 
 *   let compare a b = match a.var, b.var with
 *     | Some a, Some b -> Var.compare a b
 *     | None, None -> Expr.compare a.expr b.expr
 *     | None, _ -> -1
 *     | _, None -> 1
 *   let hash a =
 *     match a.var with
 *     | Some v -> Var.hash v
 *     | None -> match a.expr with
 *       | EVar v, _ -> Var.hash v
 *       | EAbs { tys; _ }, _ -> Hashtbl.hash tys
 *       | e, _ -> Hashtbl.hash e
 *   let equal a b =
 *     Option.equal Var.equal a.var b.var &&
 *     Expr.equal a.expr b.expr
 * end
 * 
 * module E = struct
 *   type t = string option
 *   let compare = Option.compare String.compare
 *   let default = None
 * end
 * 
 * module G = Graph.Persistent.Digraph.ConcreteLabeled(V)(E)
 * 
 * let to_graph ctx env expr =
 *   let rec aux env g = function
 *     | EApp { f = EOp { op = Log _ | ToRat_int | ToRat_mon | ToMoney_rat; _ }, _; args = [arg] }, _ -> aux env g arg
 *       (* we skip conversions *)
 *     | EVar var, _ ->
 *       let expr, env = Env.get var env in
 *       let v = { V.var = Some var; expr; label = Bindlib.name_of var } in
 *       G.add_vertex g v, v;
 *       let g, children = aux env expr
 *     | EApp { f = EOp { op; _ }, _; args } ->
 *       let v = {  } in
 *       let g, children = List.fold_left_map (aux env) g args in
 *       
 * 
 *     match expr with
 * 
 * 
 *       aux env g 
 *       (match op with
 *        | Log _ | ToRat_int | ToRat_mon | ToMoney_rat -> arg
 *     let g = G.add_vertex g v in
 *     (* Var.Set.fold (fun 
 *      * let children = Expr.free_vars expr in
 *      * let term = *)
 *     match e with
 *     | EApp { f = EOp { op; _ }; [arg] }, _ ->
 *       (match op with
 *        | Log _ | ToRat_int | ToRat_mon | ToMoney_rat -> arg (* we skip conversions *)
 *        | op -> 
 *     
 * 
 * 
 * 
 *   let rec aux env g var =
 *     let expr, env = Env.get var env in
 *     match expr with
 *     | EApp { f = EOp { op = Log _ | ToRat_int | ToRat_mon | ToMoney_rat; _ }; [arg] }, _ ->
 *       (* we skip conversions *)
 *       aux env g 
 *       (match op with
 *        | Log _ | ToRat_int | ToRat_mon | ToMoney_rat -> arg
 *     let v = { V.var; expr; label = Bindlib.name_of var } in
 *     let g = G.add_vertex g v in
 *     (* Var.Set.fold (fun 
 *      * let children = Expr.free_vars expr in
 *      * let term = *)
 *     match e with
 *     | EApp { f = EOp { op; _ }; [arg] }, _ ->
 *       (match op with
 *        | Log _ | ToRat_int | ToRat_mon | ToMoney_rat -> arg (* we skip conversions *)
 *        | op -> 
 *     
 * 
 *     Expr.format ~debug:true ctx ppf expr;
 *     Format.pp_print_cut ppf ();
 *     let vars = Var.Set.diff (Expr.free_vars expr) !already_printed in
 *     Var.Set.iter
 *       (fun v ->
 *         let { contents = e, env } = Env.find v env in
 *         let e, env = lazy_eval ctx env (result_level Var.Set.empty) e in
 *         Format.fprintf ppf "@[<hov 2>%a %a =@ %a =@ %a@]@,@," Print.punctuation
 *           "»" Print.var_debug v Expr.format
 *           (fst (lazy_eval ctx env value_level e))
 *           (aux env) e)
 *       vars;
 *     already_printed := Var.Set.union !already_printed vars;
 *     Format.pp_print_cut ppf ()
 *   in
 *   Format.pp_open_vbox ppf 2;
 *   aux env ppf expr;
 *   Format.pp_close_box ppf () *)

(* -- Plugin registration -- *)

let name = "lazy"
let extension = ".out" (* unused *)

let run link_modules optimize check_invariants ex_scope options =
  Interpreter.load_runtime_modules link_modules;
  let prg, ctx, _ =
    Driver.Passes.dcalc options ~link_modules ~optimize ~check_invariants
  in
  let scope = Driver.Commands.get_scope_uid ctx ex_scope in
  (* let result_expr, env = interpret_program prg scope in *)
  let g, base_vars, env = program_to_graph prg scope in
  to_dot stdout prg.decl_ctx env base_vars (graph_cleanup g)

(* ; * print_value_with_env prg.decl_ctx ppf env result_expr *)

let term =
  let open Cmdliner.Term in
  const run
  $ Cli.Flags.link_modules
  $ Cli.Flags.optimize
  $ Cli.Flags.check_invariants
  $ Cli.Flags.ex_scope

let () =
  Driver.Plugin.register "lazy" term
    ~doc:"Experimental lazy evaluation (plugin)"
