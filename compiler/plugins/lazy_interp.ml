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

type expr = (dcalc, untyped mark) gexpr

(* -- Definition of the lazy interpreter -- *)

let log fmt = Format.ifprintf Format.err_formatter (fmt ^^ "@\n")
let error e = Errors.raise_spanned_error (Expr.pos e)
let noassert = true

type laziness_level = {
  eval_struct : bool;
      (* if true, evaluate members of structures, tuples, etc. *)
  eval_op : bool;
      (* if false, evaluate the operands but keep e.g. `3 + 4` as is *)
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
    eval_default = true;
    eval_vars = (fun _ -> true);
  }

module Env = struct
  type t =
    | Env of (expr, elt) Var.Map.t
  and elt = { base: expr * t; mutable reduced: expr * t }

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

let rec lazy_eval :
    decl_ctx ->
    Env.t ->
    laziness_level ->
    expr ->
    expr * Env.t =
 fun ctx env llevel e0 ->
  let eval_to_value ?(eval_default = true) env e =
    lazy_eval ctx env { value_level with eval_default } e
  in
  match e0 with
  | EVar v, _ -> (
      if not llevel.eval_default
      || not (llevel.eval_vars v)
      then e0, env
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
      r, Env.join env env1)
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
              log "@[<hov 2>LET %a = %a@]@ " Print.var_debug var
                (Print.expr ~debug:true ctx)
                e;
              Env.add var e env env1)
            env (Array.to_seq vars) (List.to_seq args)
        in
        log "@]@[<hov 4>IN [%a]@]" (Print.expr ~debug:true ctx) body;
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
          (* Dirty workaround returning env from evaluate_operator *)
          let eval e =
            let e, env = lazy_eval ctx !renv llevel e in
            renv := env;
            e
          in
          Interpreter.evaluate_operator eval ctx op m args, !renv
      (* fixme: this forwards eempty *)
      | e, _ -> error e "Invalid apply on %a" (Print.expr ctx) e)
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
        lazy_eval ctx env llevel (StructField.Map.find field fields)
      | e, _ -> error e "Invalid field access on %a" (Print.expr ctx) e)
  | ETupleAccess { e; index; size }, _ -> (
    if not llevel.eval_default then e0, env
    else
      match eval_to_value env e with
      | (ETuple es, _), env when List.length es = size ->
        lazy_eval ctx env llevel (List.nth es index)
      | e, _ -> error e "Invalid tuple access on %a" (Print.expr ctx) e)
  | EMatch { e; name; cases }, _ -> (
    if not llevel.eval_default then e0, env
    else
      match eval_to_value env e with
      | (EInj { name = n; cons; e }, m), env when EnumName.equal name n ->
        lazy_eval ctx env llevel
          (EApp { f = EnumConstructor.Map.find cons cases; args = [e] }, m)
      | e, _ -> error e "Invalid match argument %a" (Print.expr ctx) e)
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
      | (ELit (LBool true), _), _ -> lazy_eval ctx env llevel cons
      | (ELit (LBool false), _), _ -> (EEmptyError, m), env
      | e, _ -> error e "Invalid exception justification %a" (Print.expr ctx) e)
    | [(e, env)] ->
      log "@[<hov 5>EVAL %a@]" (Print.expr ctx) e;
      lazy_eval ctx env llevel e
    | _ :: _ :: _ ->
      Errors.raise_multispanned_error
        ((None, Expr.mark_pos m)
        :: List.map (fun (e, _) -> None, Expr.pos e) excs)
        "Conflicting exceptions")
  | EIfThenElse { cond; etrue; efalse }, _ -> (
    match eval_to_value env cond with
    | (ELit (LBool true), _), _ -> lazy_eval ctx env llevel etrue
    | (ELit (LBool false), _), _ -> lazy_eval ctx env llevel efalse
    | e, _ -> error e "Invalid condition %a" (Print.expr ctx) e)
  | EErrorOnEmpty e, _ -> (
    match eval_to_value env e ~eval_default:false with
    | ((EEmptyError, _) as e'), _ ->
      (* This does _not_ match the eager semantics ! *)
      error e' "This value is undefined %a" (Print.expr ctx) e
    | e, env -> lazy_eval ctx env llevel e)
  | EAssert e, m -> (
    if noassert then (ELit LUnit, m), env
    else
      match eval_to_value env e with
      | (ELit (LBool true), m), env -> (ELit LUnit, m), env
      | (ELit (LBool false), _), _ ->
        error e "Assert failure (%a)" (Print.expr ctx) e
      | _ -> error e "Invalid assertion condition %a" (Print.expr ctx) e)
  | _ -> .

let result_level base_vars =
  {
    value_level with
    eval_struct = true;
    eval_op = false;
    eval_vars = (fun v -> not (Var.Set.mem v base_vars));
  }

let interpret_program
    (prg : ('dcalc, 'm mark) gexpr program)
    (scope : ScopeName.t) : ('t, 'm mark) gexpr * Env.t =
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
  log "%a" (Print.expr ~debug:true ctx) e;
  log "=====================";
  (* let m = Marked.get_mark e in *)
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
    Print.expr ~debug:true ctx ppf expr;
    Format.pp_print_cut ppf ();
    let vars = Var.Set.diff (Expr.free_vars expr) !already_printed in
    Var.Set.iter
      (fun v ->
        let e, env = (Env.find v env).reduced in
        let e, env = lazy_eval ctx env (result_level Var.Set.empty) e in
        Format.fprintf ppf "@[<hov 2>%a %a =@ %a =@ %a@]@,@," Print.punctuation
          "»" Print.var_debug v (Print.expr ctx)
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
  type t = hand_side option
  let compare = Option.compare (fun x y -> match x, y with
      | Lhs s, Lhs t | Rhs s, Rhs t -> String.compare s t
      | Lhs _, Rhs _ -> -1
      | Rhs _, Lhs _ -> 1)
  let default = None
end

module G = Graph.Persistent.Digraph.AbstractLabeled(V)(E)


let op_kind = function
    Op.Add_int_int |
    Add_rat_rat |
    Add_mon_mon |
    Add_dat_dur _ |
    Add_dur_dur
    | Sub_int_int
    | Sub_rat_rat
    | Sub_mon_mon
    | Sub_dat_dat
    | Sub_dat_dur
    | Sub_dur_dur -> `Sum
  | Mult_int_int
  | Mult_rat_rat
  | Mult_mon_rat
  | Mult_dur_int
  | Div_int_int
  | Div_rat_rat
  | Div_mon_rat
  | Div_mon_mon
  | Div_dur_dur
    -> `Product
  | Round_mon
  | Round_rat
    -> `Round
  | _ -> `Other

module GTopo = Graph.Topological.Make(G)

let to_graph ctx env expr =
  let rec aux env g e =
    (* lazy_eval ctx env (result_level base_vars) e *)
    match Expr.skip_wrappers e with
    | EApp { f = EOp { op = ToRat_int | ToRat_mon | ToMoney_rat; _ }, _;
             args = [arg] }, _ ->
      aux env g arg
    (* we skip conversions *)
    | ELit l, _ ->
      let v = G.V.create e in
      G.add_vertex g v, v
    | EVar var, _ as e ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let child, env = (Env.find var env).base in
      let g, child_v = aux env g child in
      G.add_edge g v child_v, v
    | EApp { f = EOp { op = _ ; _ }, _; args }, _ ->
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
    | _ -> Format.eprintf "%a" (Print.expr ctx) e; assert false
  in
  let base_g, _ = aux env G.empty expr in
  base_g

let program_to_graph
    (prg : ('dcalc, 'm mark) gexpr program)
    (scope : ScopeName.t) : G.t * expr Var.Set.t * Env.t =
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
  let e = match e with
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
        match Expr.skip_wrappers arg with
        | ELit _, _ -> Var.Set.add var base_vars
        | _ -> base_vars
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
      eval_vars = (fun v -> false);
    }
  in
  let rec aux (g, var_vertices, env0) e =
    let e, env0 = lazy_eval ctx env0 level e in
    match Expr.skip_wrappers e with
    | EApp { f = EOp { op = ToRat_int | ToRat_mon | ToMoney_rat; _ }, _;
             args = [arg] }, _ ->
      aux (g, var_vertices, env0) arg
    (* we skip conversions *)
    | ELit l, _ ->
      let v = G.V.create e in
      (G.add_vertex g v, var_vertices, env0), v
    | EVar var, _ as e ->
      (try (g, var_vertices, env0), Var.Map.find var var_vertices
       with Not_found ->
         let v = G.V.create e in
         let g = G.add_vertex g v in
         let child, env = (Env.find var env0).base in
         let (g, var_vertices, env), child_v =
           aux (g, var_vertices, (Env.join env0 env)) child in
         let var_vertices =
           let rec is_lit v =
             match G.V.label v with
             | ELit _, _ -> true
             | EVar var, _ -> (match G.succ g v with [v] -> is_lit v | _ -> false)
             | _ -> false
           in
           if is_lit child_v then var_vertices
           else Var.Map.add var v var_vertices
         in
         (G.add_edge g v child_v, var_vertices, env), v)
    | EApp { f = EOp { op; _ }, _; args = [lhs; rhs]}, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), lhs = aux (g, var_vertices, env0) lhs in
      let (g, var_vertices, env), rhs = aux (g, var_vertices, env) rhs in
      let lhs_label, rhs_label = match op with
        | Add_int_int
        | Add_rat_rat
        | Add_mon_mon
        | Add_dat_dur _
        | Add_dur_dur
          -> Some (E.Lhs "⊕"), Some (E.Rhs "⊕")
        | Sub_int_int | Sub_rat_rat | Sub_mon_mon | Sub_dat_dat
        | Sub_dat_dur | Sub_dur_dur -> Some (E.Lhs "⊕"), Some (E.Rhs "⊖")
        | Mult_int_int
        | Mult_rat_rat
        | Mult_mon_rat
        | Mult_dur_int
          -> Some (E.Lhs "⊗"), Some (E.Rhs "⊗")
        | Div_int_int | Div_rat_rat | Div_mon_rat | Div_mon_mon | Div_dur_dur
          -> Some (E.Lhs "⊗"), Some (E.Rhs "⊘")
        | _ -> None, None
      in
      let g = G.add_edge_e g (G.E.create v lhs_label lhs) in
      let g = G.add_edge_e g (G.E.create v rhs_label rhs) in
      (g, var_vertices, env), v
    | EApp { f = EOp { op = _ ; _ }, _; args }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let (g, var_vertices, env), children =
        List.fold_left_map aux (g, var_vertices, env0) args
      in
      (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env), v
    | EInj { e; _ }, _ -> aux (g, var_vertices, env0) e
    | EStruct { fields; _ }, _ ->
      let v = G.V.create e in
      let g = G.add_vertex g v in
      let args = List.map snd (StructField.Map.bindings fields) in
      let (g, var_vertices, env), children =
        List.fold_left_map aux (g, var_vertices, env0) args
      in
      (List.fold_left (fun g -> G.add_edge g v) g children, var_vertices, env), v
    | _ -> Format.eprintf "%a" (Print.expr ctx) e; assert false
  in
  let (g, _, env), _ = aux (G.empty, Var.Map.empty, env) e in
  Format.eprintf "BASE: @[<v>%a@]" (Format.pp_print_list Print.var) (Var.Set.elements base_vars);
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
  G.fold_edges_e (fun e g ->
      G.add_edge_e (G.remove_edge_e g e)
        (G.E.create (G.E.dst e) (G.E.label e) (G.E.src e)))
    g g

let rec graph_cleanup g =
  let g =
    let module GCtr = Graph.Contraction.Make(G) in
    GCtr.contract (fun e ->
      G.E.label e = None &&
      match G.V.label (G.E.src e), G.V.label (G.E.dst e) with
      | (EVar _, _), (EVar _, _) -> true
      | (EApp { f = EOp { op = op1; _}, _; args = [_; _] }, _),
        (EApp { f = EOp { op = op2; _}, _; args = [_; _] }, _)
        ->
        (match op_kind op1, op_kind op2 with
         | `Sum, `Sum -> true
         | `Prod, `Prod -> true
         | _ -> false)
      | _ -> false)
    g
  in
  let g =
    G.fold_vertex (fun v g ->
        match G.V.label v, List.map G.V.label (G.pred g v) with
        (* | (ELit _, _), [EVar _, _] -> G.remove_vertex g v *)
        | (ELit _, _), _ -> G.remove_vertex g v (* test with print full form. *)
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

let to_dot oc ctx env base_vars g =
  let module GPr = Graph.Graphviz.Dot(struct
      include G
      let graph_attributes _ = [(* `Rankdir `LeftToRight *)]
      let default_vertex_attributes _ = []
      let vertex_label v = match Expr.skip_wrappers (G.V.label v) with
        | EVar v, _ as e ->
          (match lazy_eval ctx env value_level e with
           | (ELit l, _), _ ->
             Format.asprintf "%s\n%a" (Bindlib.name_of v) Print.lit l
           | _ ->
             Format.asprintf "%s" (Bindlib.name_of v))
        | EApp { f = EOp { op; _}, _; _ }, _ as e ->
          (match op_kind op with
           | `Sum | `Product -> Format.asprintf "%a" (Print.expr ctx) e
           (* | `Product -> "" *)
           | `Round -> "<round>"
           | `Other -> Format.asprintf "<%a>" Print.operator op)
        | EApp { f; _ }, _ ->
          Format.asprintf "%a" (Print.expr_debug ~debug:false) f
        | ELit l, _ -> Format.asprintf "%a" Print.lit l
        | EStruct {name; _}, _ -> Format.asprintf "{%a}" StructName.format_t name
        | z -> Format.asprintf "[%a]" (Print.expr_debug ~debug:false) z
      let vertex_name v = Printf.sprintf "x%03d" (G.V.hash v)

      let vertex_attributes v =
        `Label (vertex_label v) ::
        match G.V.label v with
        | EVar v, _ when Var.Set.mem v base_vars ->
          [ `Color 0x5588ff; `Shape `Box ]
        | EApp { f = EOp { op; _}, _; _ }, _ ->
          (match op_kind op with
           | `Sum | `Product -> [ `Shape `Box ]
           | _ -> [])
        | _ -> []
      let get_subgraph v =
        match G.V.label v with
        | EVar v, _ when Var.Set.mem v base_vars ->
          Some {
            Graph.Graphviz.DotAttributes.sg_name = "inputs";
   	    sg_attributes = [`Shape `Box];
            sg_parent = None;
          }
        | _ -> None
      let default_edge_attributes _ = []
      let edge_attributes e = match E.label e with
        | Some (Lhs s | Rhs s) -> [ `Label s; `Color 0xbb7700 ]
        | None -> []
    end)
  in
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
  *    FTra.fold (fun v ->  *)

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
 *     Print.expr ~debug:true ctx ppf expr;
 *     Format.pp_print_cut ppf ();
 *     let vars = Var.Set.diff (Expr.free_vars expr) !already_printed in
 *     Var.Set.iter
 *       (fun v ->
 *         let { contents = e, env } = Env.find v env in
 *         let e, env = lazy_eval ctx env (result_level Var.Set.empty) e in
 *         Format.fprintf ppf "@[<hov 2>%a %a =@ %a =@ %a@]@,@," Print.punctuation
 *           "»" Print.var_debug v (Print.expr ctx)
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


let apply ~source_file ~output_file ~scope prg _type_ordering =
  let scope =
    match scope with
    | None -> Errors.raise_error "A scope must be specified"
    | Some s -> s
  in
  ignore source_file;
  (* File.with_formatter_of_opt_file output_file
   * @@ fun fmt -> *)
  ignore output_file;
  (* let ppf = Format.std_formatter in *)
  (* let result_expr, env = interpret_program prg scope in *)
  let g, base_vars, env = program_to_graph prg scope in
  to_dot stdout prg.decl_ctx env base_vars (graph_cleanup g)

(* ;
   * print_value_with_env prg.decl_ctx ppf env result_expr *)

let () = Driver.Plugin.register_dcalc ~name ~extension apply
