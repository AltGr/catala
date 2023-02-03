(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2020 Inria, contributor:
   Denis Merigoux <denis.merigoux@inria.fr>, Emile Rolley <emile.rolley@tuta.io>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

(** Reference interpreter for the default calculus *)

open Catala_utils
open Shared_ast
module Runtime = Runtime_ocaml.Runtime

type lit = dcalc glit
module LitSet = Set.Make (struct type t = lit let compare = Expr.compare_lit end)

module Dom = struct
  type values =
    | Set of LitSet.t
    | Range of lit * lit (** (a, b) with a <= b TODO add -inf, +inf and remove Any *)
    | Any

  type 'm v = { v: values; depends: (dcalc, 'm mark) gexpr Var.Set.t }

  type 'm t =
    | Lit of 'm v
    | Func of 'm Ast.expr (* function or operator, can use free variables *)
    | Struct of StructName.t * 'm t StructField.Map.t
    | Tuple of 'm t list
    | Array of 'm t * int * int (* approx of all values, range for length *)
    | Enum of EnumName.t * 'm t EnumConstructor.Map.t (* any of the cases *)
    | Unknown of (dcalc, 'm mark) gexpr Var.Set.t (* dependencies *)

  let memv lit = function
    | Set s -> LitSet.mem lit s
    | Range (a, b) -> Expr.compare_lit a lit <= 0 && Expr.compare_lit lit b <= 0
    | Any -> true

  let minlit l1 l2 = if Expr.compare_lit l1 l2 <= 0 then l1 else l2
  let maxlit l1 l2 = if Expr.compare_lit l1 l2 <= 0 then l2 else l1

  (* f is assumed monotonic *)
  let mapv f = function
    | Any -> Any
    | Set s -> Set (LitSet.map f s)
    | Range (a, b) ->
      let a = f a and b = f b in
      if Expr.compare_lit a b <= 0 then Range (a, b) else Range (b, a)

  let split_range = function
    | LInt l, LInt u ->
      let zero = LInt (Runtime.integer_of_int 0) in
      (if Expr.compare_lit (LInt l) zero < 0 then Some (LInt l, zero) else None),
      (if Expr.compare_lit (LInt u) zero >= 0 then Some (zero, LInt u) else None)
    | LRat l, LRat u ->
      let zero = LRat (Runtime.decimal_of_float 0.) in
      (if Expr.compare_lit (LRat l) zero < 0 then Some (LRat l, zero) else None),
      (if Expr.compare_lit (LRat u) zero >= 0 then Some (zero, LRat u) else None)
    | LMoney l, LMoney u ->
      let zero = LMoney (Runtime.money_of_units_int 0) in
      (if Expr.compare_lit (LMoney l) zero < 0 then Some (LMoney l, zero) else None),
      (if Expr.compare_lit (LMoney u) zero >= 0 then Some (zero, LMoney u) else None)
    | LDuration l, LDuration u -> (* FIXME: comparison of durations may be incorrect *)
      let zero = LDuration (Runtime.duration_of_numbers 0 0 0) in
      (if Expr.compare_lit (LDuration l) zero < 0 then Some (LDuration l, zero) else None),
      (if Expr.compare_lit (LDuration u) zero >= 0 then Some (zero, LDuration u) else None)
    | _ -> failwith "split"

  let to_range = function
    | Set s when not (LitSet.is_empty s) -> Some (LitSet.min_elt s, LitSet.max_elt s)
    | Range (l, u) -> Some (l, u)
    | _ -> None

  let cleanup = function Range (l, u) when Expr.equal_lit l u -> Set (LitSet.singleton l) | v -> v

  (* Assumes f is monotonic in va, vb when they are of constant sign *)
  let app2 f va vb =
    let merge rng1 rng2 = match rng1, rng2 with
      | None, _ | _, None -> None
      | Some (l1, u1),  Some (l2, u2) -> Some (minlit l1 l2, maxlit u1 u2)
    in
    let frange rnga rngb = match rnga, rngb with
      | None, _ | _, None -> None
      | Some rnga, Some rngb ->
        let rnga_neg, rnga_pos = split_range rnga in
        let rngb_neg, rngb_pos = split_range rngb in
        let mapf ra rb = match ra, rb with
          | None, _ | _, None -> None
          | Some (l1, u1), Some (l2, u2) ->
            List.fold_left (fun rng retf ->
                merge rng (Some (retf, retf)))
              None [f l1 l2; f u1 u2; f l1 u2; f u1 l2]
        in
        List.fold_left (fun r (ra, rb) -> merge r (mapf ra rb))
          None
          [rnga_neg, rngb_neg; rnga_pos, rngb_pos; rnga_neg, rngb_pos; rnga_pos, rngb_neg]
    in
    match cleanup va, cleanup vb with
    | Set sa, Set sb ->
      let na = LitSet.cardinal sa and nb = LitSet.cardinal sb in
      if na = 0 || nb = 0 then Set LitSet.empty
      else if na = 1 then
        let a = LitSet.choose sa in
        Set (LitSet.fold (fun b -> LitSet.add (f a b)) sb LitSet.empty)
      else if nb = 1 then
        let b = LitSet.choose sb in
        Set (LitSet.fold (fun a -> LitSet.add (f a b)) sa LitSet.empty)
      else
        let rnga = LitSet.min_elt sa, LitSet.max_elt sa in
        let rngb = LitSet.min_elt sb, LitSet.max_elt sb in
        (match frange (Some rnga) (Some rngb) with
         | None -> Set (LitSet.empty)
         | Some (l, u) -> Range (l, u))
    | Range (mina, maxa), Range (minb, maxb) ->
      (match frange (Some (mina, maxa)) (Some (minb, maxb)) with
       | None -> Set (LitSet.empty)
       | Some (l, u) -> Range (l, u))
    | Set sa, Range (minb, maxb) ->
      (match LitSet.fold (fun a -> merge (frange (Some (a,a)) (Some (minb,maxb)))) sa None with
       | None -> Set (LitSet.empty)
       | Some (l, u) -> Range (l, u))
    | Range (mina, maxa), Set sb ->
      (match LitSet.fold (fun b -> merge (frange (Some (mina,maxa)) (Some (b,b)))) sb None with
       | None -> Set (LitSet.empty)
       | Some (l, u) -> Range (l, u))
    | Any, _ | _, Any -> Any

  let fold_child f acc = function
    | Lit _ | Func _ | Unknown _ -> acc
    | Struct (_, fmap) -> StructField.Map.fold (fun _ v acc -> f acc v) fmap acc
    | Tuple l -> List.fold_left f acc l
    | Array (t, _nmin, _nmax) -> f acc t
    | Enum (_, cmap) -> EnumConstructor.Map.fold (fun _ v acc -> f acc v) cmap acc

  let map_child f = function
    | (Lit _ | Func _ | Unknown _) as t -> t
    | Struct (sname, fmap) ->
      Struct (sname, StructField.Map.map f fmap)
    | Tuple l -> Tuple (List.map f l)
    | Array (t, nmin, nmax) -> Array (f t, nmin, nmax)
    | Enum (ename, cmap) ->
      Enum (ename, EnumConstructor.Map.map f cmap)

  let rec depends = function
    | Lit {depends; _} | Unknown depends -> depends
    | Func _ -> Var.Set.empty
    | t -> fold_child (fun acc t -> Var.Set.union acc (depends t)) Var.Set.empty t

  let rec add_depend dep = function
    | Lit v -> Lit { v with depends = Var.Set.add dep v.depends }
    | Func e -> Func e
    | Unknown depends -> Unknown (Var.Set.add dep depends)
    | t -> map_child (add_depend dep) t

  let format_approx ppf = function
    | Set s ->
      Format.fprintf ppf "@[<hv 2>[ %a ]@]"
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " |@ ")
           Print.lit)
        (LitSet.elements s)
    | Range (l1, l2) ->
      Format.fprintf ppf "@[<hv 1>[%a..@,%a]@]" Print.lit l1 Print.lit l2
    | Any -> Format.pp_print_char ppf '?'

  let rec format ppf = function
    | Func e -> (match Marked.unmark e with
        | EOp { op; _ } -> Print.operator ppf op
        | _ -> Format.pp_print_string ppf "<fun>")
    | Lit { v; _} -> format_approx ppf v
    | Struct (sname, fmap) ->
      Format.fprintf ppf "@[<hov 2>%a {@ %a@ }@]"
        StructName.format_t sname
        (Format.pp_print_list ~pp_sep:Format.pp_print_space
           (fun ppf (fname, v) ->
              Format.fprintf ppf "@[<hov 3>-- %a: %a@]"
                StructField.format_t fname format v))
        (StructField.Map.bindings fmap)
    | Enum (ename, vmap) ->
      (match EnumConstructor.Map.bindings vmap with
       | [ econs, v ] ->
         Format.fprintf ppf "@[<hov 2>%a.%a@ %a@]"
           EnumName.format_t ename
           EnumConstructor.format_t econs
           format v
       | vbind ->
         Format.fprintf ppf "@[<hov 2>%a.{%a}@]"
           EnumName.format_t ename
           (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf " |@ ")
              (fun ppf (econs, v) ->
                 Format.fprintf ppf "@[<hov 2>%a %a@]"
                   EnumConstructor.format_t econs
                   format v))
           vbind)
    | Tuple vl ->
      Format.fprintf ppf "@[<hov 1>(%a)@]"
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ",@ ")
           format)
        vl
    | Array (t, nmin, nmax) ->
      Format.fprintf ppf "@[<hov 1>[@,%a@,]{%s}@]"
        format t
        (if nmin = nmax then string_of_int nmin else Printf.sprintf "%d-%d" nmin nmax)
    | Unknown _ -> Format.pp_print_string ppf "?"


  let union_approx a1 a2 =
    match a1, a2 with
    | Any, _ | _, Any -> Any
    | Set s1, Set s2 -> Set (LitSet.union s1 s2)
    | Range (from1, until1), Range (from2, until2) -> Range (minlit from1 from2, maxlit until1 until2)
    | Set s, Range (from, until) | Range (from, until), Set s ->
      Range (minlit (LitSet.min_elt s) from, maxlit (LitSet.max_elt s) until)

  let rec union_v v1 v2 =
    { v = union_approx v1.v v2.v; depends = Var.Set.union v1.depends v2.depends }

  let rec union v1 v2 = match v1, v2 with
    | Lit l1, Lit l2 -> Lit (union_v l1 l2)
    | Struct (sname, fields1), Struct (sname2, fields2) when StructName.equal sname sname2 ->
      Struct (sname, StructField.Map.mapi
                (fun fname v -> union v (StructField.Map.find fname fields2)) fields1)
    | Enum (ename, vmap1), Enum (ename2, vmap2) when EnumName.equal ename ename2 ->
      Enum (ename, EnumConstructor.Map.merge (fun _ v1 v2 -> match v1, v2 with
          | v, None | None, v -> v
          | Some v1, Some v2 -> Some (union v1 v2))
          vmap1 vmap2)
    | Array (t1, nmin1, nmax1), Array (t2, nmin2, nmax2) ->
      Array (union t1 t2, min nmin1 nmin2, max nmax1 nmax2)
    | _, _ -> Unknown (Var.Set.union (depends v1) (depends v2))
  (* Likely a type error ? *)

  let empty = Lit { v = Set LitSet.empty; depends = Var.Set.empty }
end

type 'm env = ('m Ast.expr, 'm Dom.t) Var.Map.t

(** {1 Helpers} *)

let is_empty_error (e : 'm Ast.expr) : bool =
  match Marked.unmark e with ELit LEmptyError -> true | _ -> false

let log_indent = ref 0

(** {1 Evaluation} *)

let print_log ctx entry infos pos e =
  if !Cli.trace_flag then
    match entry with
    | VarDef _ ->
      (* TODO: this usage of Format is broken, Formatting requires that all is
         formatted in one pass, without going through intermediate "%s" *)
      Cli.log_format "%*s%a %a: %s" (!log_indent * 2) "" Print.log_entry entry
        Print.uid_list infos
        (match Marked.unmark e with
        | EAbs _ -> Cli.with_style [ANSITerminal.green] "<function>"
        | _ ->
          let expr_str =
            Format.asprintf "%a" (Expr.format ctx ~debug:false) e
          in
          let expr_str =
            Re.Pcre.substitute ~rex:(Re.Pcre.regexp "\n\\s*")
              ~subst:(fun _ -> " ")
              expr_str
          in
          Cli.with_style [ANSITerminal.green] "%s" expr_str)
    | PosRecordIfTrueBool -> (
      match pos <> Pos.no_pos, Marked.unmark e with
      | true, ELit (LBool true) ->
        Cli.log_format "%*s%a%s:\n%s" (!log_indent * 2) "" Print.log_entry entry
          (Cli.with_style [ANSITerminal.green] "Definition applied")
          (Cli.add_prefix_to_each_line (Pos.retrieve_loc_text pos) (fun _ ->
               Format.asprintf "%*s" (!log_indent * 2) ""))
      | _ -> ())
    | BeginCall ->
      Cli.log_format "%*s%a %a" (!log_indent * 2) "" Print.log_entry entry
        Print.uid_list infos;
      log_indent := !log_indent + 1
    | EndCall ->
      log_indent := !log_indent - 1;
      Cli.log_format "%*s%a %a" (!log_indent * 2) "" Print.log_entry entry
        Print.uid_list infos

let rec evaluate_expr (ctx : decl_ctx) (env: 'm env) (e : 'm Ast.expr) : 'm Dom.t =
  match Marked.unmark e with
  | ELit l -> Lit {v = Set (LitSet.singleton l); depends = Var.Set.empty}
  | EVar v ->
    (match Var.Map.find_opt v env with
     | Some t -> Dom.add_depend v t
     | None -> Unknown (Var.Set.singleton v))
  | EApp { f = e1; args } ->
    let fs = evaluate_expr ctx env e1 in
    let args = List.map (evaluate_expr ctx env) args in
    eval_app ctx env fs args
  | EAbs _ | EOp _ -> Func e (* todo: depends on the free variables in e ? *)
  | EStruct { fields; name } ->
    Struct (name, StructField.Map.map (evaluate_expr ctx env) fields)
  | EStructAccess { e = e1; name = s; field } -> (
    match evaluate_expr ctx env e1 with
    | Struct (sname, fmap) when StructName.equal s sname ->
      StructField.Map.find field fmap
    | d -> Unknown (Dom.depends d))
  | ELit LEmptyError -> Lit { v = Set (LitSet.singleton LEmptyError); depends = Var.Set.empty } (* ??? *)
  | ETuple es -> Tuple (List.map (evaluate_expr ctx env) es)
  | ETupleAccess { e = e1; index; size } ->
    (match evaluate_expr ctx env e1 with
     | Tuple dl when List.length dl = size -> List.nth dl index
     | d -> Unknown (Dom.depends d))
  | EInj { e; name; cons } ->
    let d = evaluate_expr ctx env e in
    Enum (name, EnumConstructor.Map.singleton cons d)
  | EMatch { e; cases; name } -> (
      match evaluate_expr ctx env e with
      | Enum (ename, cmap) when EnumName.equal ename name ->
        EnumConstructor.Map.fold (fun c handler d ->
            match EnumConstructor.Map.find_opt c cmap with
            | None -> d (* match case could be eliminated *)
            | Some dcase ->
              Dom.union d (eval_app ctx env (Dom.Func handler) [dcase])
          )
          cases Dom.empty
      | d ->
        Unknown (EnumConstructor.Map.fold
                   (fun _ e -> Var.Set.union (Dom.depends (evaluate_expr ctx env e)))
                   cases
                   (Dom.depends d))
        (* We could just join all cases with an unknown parameter for more info here ? *)
    )
  | EIfThenElse { cond; etrue; efalse } -> (
      match evaluate_expr ctx env cond with
      | Lit {v; depends} ->
        let d1 =
          if Dom.memv (LBool true) v then evaluate_expr ctx env etrue else Dom.empty
        in
        let d2 =
          if Dom.memv (LBool false) v then evaluate_expr ctx env efalse else Dom.empty
        in
        Dom.union (Dom.union d1 d2) (Lit {v=Set LitSet.empty; depends})
      | d -> Unknown (Var.Set.union (Dom.depends d) (Var.Set.union (Dom.depends (evaluate_expr ctx env etrue)) (Dom.depends (evaluate_expr ctx env efalse))))
    )
  | EArray es ->
    let len = List.length es in
    Array (List.fold_left (fun d e -> Dom.union d (evaluate_expr ctx env e)) Dom.empty es,
           len, len)
  | EErrorOnEmpty e' ->
    let e' = evaluate_expr ctx env e' in
    if Marked.unmark e' = ELit LEmptyError then
      Errors.raise_spanned_error (Expr.pos e')
        "This variable evaluated to an empty term (no rule that defined it \
         applied in this situation)"
    else e'
  | EAssert e' -> (
    match Marked.unmark (evaluate_expr ctx env e') with
    | ELit (LBool true) -> Marked.same_mark_as (ELit LUnit) e'
    | ELit (LBool false) -> (
      match Marked.unmark e' with
      | EErrorOnEmpty
          ( EApp
              {
                f = EOp { op; _ }, _;
                args = [((ELit _, _) as e1); ((ELit _, _) as e2)];
              },
            _ ) ->
        Errors.raise_spanned_error (Expr.pos e') "Assertion failed: %a %a %a"
          (Expr.format ctx ~debug:false)
          e1 Print.operator op
          (Expr.format ctx ~debug:false)
          e2
      | EApp
          {
            f = EOp { op = Log _; _ }, _;
            args =
              [
                ( EApp
                    {
                      f = EOp { op; _ }, _;
                      args = [((ELit _, _) as e1); ((ELit _, _) as e2)];
                    },
                  _ );
              ];
          } ->
        Errors.raise_spanned_error (Expr.pos e') "Assertion failed: %a %a %a"
          (Expr.format ctx ~debug:false)
          e1 Print.operator op
          (Expr.format ctx ~debug:false)
          e2
      | EApp
          {
            f = EOp { op; _ }, _;
            args = [((ELit _, _) as e1); ((ELit _, _) as e2)];
          } ->
        Errors.raise_spanned_error (Expr.pos e') "Assertion failed: %a %a %a"
          (Expr.format ctx ~debug:false)
          e1 Print.operator op
          (Expr.format ctx ~debug:false)
          e2
      | _ ->
        Cli.debug_format "%a" (Expr.format ctx) e';
        Errors.raise_spanned_error (Expr.pos e') "Assertion failed")
    | ELit LEmptyError -> Marked.same_mark_as (ELit LEmptyError) e
    | _ ->
      Errors.raise_spanned_error (Expr.pos e')
        "Expected a boolean literal for the result of this assertion (should \
         not happen if the term was well-typed)")
  | EDefault { excepts; just; cons } -> (
    let excepts = List.map (evaluate_expr ctx env) excepts in


    let empty_count = List.length (List.filter is_empty_error excepts) in
    match List.length excepts - empty_count with
    | 0 -> (
      let just = evaluate_expr ctx env just in
      match Marked.unmark just with
      | ELit LEmptyError -> Marked.same_mark_as (ELit LEmptyError) e
      | ELit (LBool true) -> evaluate_expr ctx env cons
      | ELit (LBool false) -> Marked.same_mark_as (ELit LEmptyError) e
      | _ ->
        Errors.raise_spanned_error (Expr.pos e)
          "Default justification has not been reduced to a boolean at \
           evaluation (should not happen if the term was well-typed")
    | 1 -> List.find (fun sub -> not (is_empty_error sub)) excepts
    | _ ->
      Errors.raise_multispanned_error
        (List.map
           (fun except ->
             Some "This consequence has a valid justification:", Expr.pos except)
           (List.filter (fun sub -> not (is_empty_error sub)) excepts))
        "There is a conflict between multiple valid consequences for assigning \
         the same variable.")

and eval_app ctx env df arg_doms = match df with
  | Dom.Func (EAbs { binder; _ }, _) ->
    let v_args, f_body = Bindlib.unmbind binder in
    let env =
      List.fold_left2 (fun env v x -> Var.Map.add v x env) env (Array.to_list v_args) arg_doms
    in
    evaluate_expr ctx env f_body
  | Dom.Func (EOp {op; _}, _) -> evaluate_operator ctx env op arg_doms
  | fs -> Unknown (Dom.depends fs) (* type error ? *)

and evaluate_operator :
    type k.
    decl_ctx ->
    'm env ->
    (dcalc, k) operator ->
    'm Dom.t list ->
    'm Dom.t =
  fun ctx env op args ->
  let depends =
    List.fold_left (fun acc d -> Var.Set.union (Dom.depends d) acc) Var.Set.empty args
  in
  let rlit v =
    Dom.Lit {v; depends}
  in
  Operator.kind_dispatch op
    ~monomorphic:(fun op ->
        match op, args with
        | Not, [Lit {v=a;_}] ->
          LitSet.empty |>
          (if Dom.memv (LBool true) a then LitSet.add (LBool false) else Fun.id) |>
          (if Dom.memv (LBool true) a then LitSet.add (LBool true) else Fun.id) |>
          fun s -> rlit (Dom.Set s)
        | And, [Lit {v=a;_}; Lit {v=b;_}] ->
          if not (Dom.memv (LBool true) a) || not (Dom.memv (LBool true) b)
          then rlit (Dom.Set (LitSet.singleton (LBool false)))
          else if not (Dom.memv (LBool false) a) && not (Dom.memv (LBool false) b)
          then rlit (Dom.Set (LitSet.singleton (LBool true)))
          else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
        | Or, [Lit {v=a;_}; Lit {v=b;_}] ->
          if not (Dom.memv (LBool true) a) && not (Dom.memv (LBool true) b)
          then rlit (Dom.Set (LitSet.singleton (LBool false)))
          else if not (Dom.memv (LBool false) a) || not (Dom.memv (LBool false) b)
          then rlit (Dom.Set (LitSet.singleton (LBool true)))
          else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
        | Xor, [Lit {v=a;_}; Lit {v=b;_}] ->
          let tpa = Dom.memv (LBool true) a and tfa = Dom.memv (LBool false) a in
          let tpb = Dom.memv (LBool true) b and tfb = Dom.memv (LBool false) b in
          if not tpa && not tfb || not tfa && not tpb
          then rlit (Dom.Set (LitSet.singleton (LBool true)))
          else if not tpa && not tpb || not tfa && not tfb
          then rlit (Dom.Set (LitSet.singleton (LBool false)))
          else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
        | GetDay, [_] -> rlit (Dom.Range (LInt (Runtime.integer_of_int 1), LInt (Runtime.integer_of_int 1)))
        | GetMonth, [_] -> rlit (Dom.Range (LInt (Runtime.integer_of_int 1), LInt (Runtime.integer_of_int 12)))
        | GetYear, [_] -> rlit Dom.Any
        | FirstDayOfMonth, [_] -> rlit Dom.Any
        | LastDayOfMonth, [_] -> rlit Dom.Any
        | ( ( Not | GetDay | GetMonth | GetYear | FirstDayOfMonth
            | LastDayOfMonth | And | Or | Xor ),
            _ ) ->
          rlit Dom.Any)
    ~polymorphic:(fun op ->
        match op, args with
        | Length, [Array (_, nmin, nmax)] ->
          rlit (Dom.Range (LInt (Runtime.integer_of_int nmin), LInt (Runtime.integer_of_int nmax)))
        | Log _, [d] -> d
        | Eq, [a; b] ->
          (match a, b with
           | Lit {v=Set sa;_}, Lit {v=Set sb; _} when LitSet.cardinal sa = 1 && LitSet.equal sa sb ->
             rlit (Dom.Set (LitSet.singleton (LBool true)))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | Map, [ef; Array (da, nmin, nmax)] ->
          Array (eval_app ctx env ef [da], nmin, nmax)
        | Reduce, [df; default; Array (da, nmin, nmax)] ->
          if nmax = 0 then default else
          let d0 =
            if nmin > 0 then rlit (Set (LitSet.empty))
            else default (* FIXME: add depends ? *)
          in
          let dn = eval_app ctx env df [da] in
          Dom.union d0 dn
        | Concat, [Array (d1, nmin1, nmax1); Array (d2, nmin2, nmax2)] ->
          Array (Dom.union d1 d2, nmin1 + nmin2, nmax1 + nmax2)
        | Filter, [_; Array (d, _, nmax)] ->
          Array (d, 0, nmax)
        | Fold, [f; init; Array (d, _, nmax)] ->
          if nmax = 0 then init
          else Dom.union init (eval_app ctx env f [init; d])
        | (Length | Log _ | Eq | Map | Concat | Filter | Fold | Reduce), _ ->
          rlit Dom.Any)
    ~resolved:(fun op ->
        let rmap d f = match d with
          | Dom.Lit {v;depends} ->
            (try Dom.Lit {v=Dom.mapv f v; depends} with Exit -> Dom.Lit {v=Dom.Any; depends})
          | _ -> rlit Dom.Any
        in
        match op, args with
        | Minus_int, [d] ->
          rmap d (function LInt i -> LInt (Runtime.Oper.o_minus_int i)
                         | _ -> raise Exit)
        | Minus_rat, [d] ->
          rmap d (function LRat r -> LRat (Runtime.Oper.o_minus_rat r)
                         | _ -> raise Exit)
        | Minus_mon, [d] ->
          rmap d (function LMoney m -> LMoney (Runtime.Oper.o_minus_mon m)
                         | _ -> raise Exit)
        | Minus_dur, [d] ->
          rmap d (function LDuration d -> LDuration (Runtime.Oper.o_minus_dur d)
                         | _ -> raise Exit)
        | ToRat_int, [d] ->
          rmap d (function LInt i -> LRat (Runtime.Oper.o_torat_int i)
                         | _ -> raise Exit)
        | ToRat_mon, [d] ->
          rmap d (function LMoney m -> LRat (Runtime.Oper.o_torat_mon m)
                         | _ -> raise Exit)
        | ToMoney_rat, [d] ->
          rmap d (function LRat r -> LMoney (Runtime.Oper.o_tomoney_rat r)
                         | _ -> raise Exit)
        | Round_rat, [d] ->
          rmap d (function LRat r -> LRat (Runtime.Oper.o_round_rat r)
                         | _ -> raise Exit)
        | Round_mon, [d] ->
          rmap d (function LMoney m -> LMoney (Runtime.Oper.o_round_mon m)
                         | _ -> raise Exit)
        | Add_int_int, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LInt a, LInt b -> LInt (Runtime.Oper.o_add_int_int a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Add_rat_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LRat a, LRat b -> LRat (Runtime.Oper.o_add_rat_rat a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Add_mon_mon, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LMoney a, LMoney b -> LMoney (Runtime.Oper.o_add_mon_mon a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Add_dat_dur, [_; _] -> rlit Dom.Any
        | Add_dur_dur, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LDuration a, LDuration b -> LDuration (Runtime.Oper.o_add_dur_dur a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Sub_int_int, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LInt a, LInt b -> LInt (Runtime.Oper.o_sub_int_int a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Sub_rat_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LRat a, LRat b -> LRat (Runtime.Oper.o_sub_rat_rat
 a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Sub_mon_mon, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LMoney a, LMoney b -> LMoney (Runtime.Oper.o_sub_mon_mon a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Sub_dat_dat, [_; _] -> rlit Dom.Any
        | Sub_dat_dur, [_; _] -> rlit Dom.Any
        | Sub_dur_dur, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LDuration a, LDuration b -> LDuration (Runtime.Oper.o_sub_dur_dur a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Mult_int_int, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LInt a, LInt b -> LInt (Runtime.Oper.o_mult_int_int a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Mult_rat_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LRat a, LRat b -> LRat (Runtime.Oper.o_mult_rat_rat a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Mult_mon_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LMoney a, LRat b -> LMoney (Runtime.Oper.o_mult_mon_rat a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Mult_dur_int, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LDuration a, LInt b -> LDuration (Runtime.Oper.o_mult_dur_int a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Div_int_int, [Lit d1; Lit d2] -> (* TODO: extend ranges for inf *)
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LInt a, LInt b -> LRat (Runtime.Oper.o_div_int_int a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Div_rat_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LRat a, LRat b -> LRat (Runtime.Oper.o_div_rat_rat a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Div_mon_mon, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LMoney a, LMoney b -> LRat (Runtime.Oper.o_div_mon_mon a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | Div_mon_rat, [Lit d1; Lit d2] ->
          rlit (Dom.app2 (fun va vb ->
              match va, vb with
              | LMoney a, LRat b -> LMoney (Runtime.Oper.o_div_mon_rat a b)
              | _ -> raise Exit)
              d1.v d2.v)
        | ( Lt_int_int
          | Lt_rat_rat
          | Lt_mon_mon
          | Lt_dat_dat
          | Lt_dur_dur ), [Lit d1; Lit d2] ->
          (match Dom.to_range d1.v, Dom.to_range d2.v with
           | Some (mina, maxa), Some (minb, maxb) ->
             if Expr.compare_lit maxa minb < 0 then rlit (Dom.Set (LitSet.singleton (LBool true)))
             else if Expr.compare_lit mina maxb >= 0 then rlit (Dom.Set (LitSet.singleton (LBool false)))
             else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | (Lte_int_int
          | Lte_rat_rat
          | Lte_mon_mon
          | Lte_dat_dat
          | Lte_dur_dur), [Lit d1; Lit d2] ->
          (match Dom.to_range d1.v, Dom.to_range d2.v with
           | Some (mina, maxa), Some (minb, maxb) ->
             if Expr.compare_lit maxa minb <= 0 then rlit (Dom.Set (LitSet.singleton (LBool true)))
             else if Expr.compare_lit mina maxb > 0 then rlit (Dom.Set (LitSet.singleton (LBool false)))
             else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | (Gt_int_int
          | Gt_rat_rat
          | Gt_mon_mon
          | Gt_dat_dat
          | Gt_dur_dur), [Lit d1; Lit d2] ->
          (match Dom.to_range d1.v, Dom.to_range d2.v with
           | Some (mina, maxa), Some (minb, maxb) ->
             if Expr.compare_lit mina maxb > 0 then rlit (Dom.Set (LitSet.singleton (LBool true)))
             else if Expr.compare_lit maxa minb <= 0 then rlit (Dom.Set (LitSet.singleton (LBool false)))
             else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | (Gte_int_int
          | Gte_rat_rat
          | Gte_mon_mon
          | Gte_dat_dat
          | Gte_dur_dur), [Lit d1; Lit d2] ->
          (match Dom.to_range d1.v, Dom.to_range d2.v with
           | Some (mina, maxa), Some (minb, maxb) ->
             if Expr.compare_lit mina maxb >= 0 then rlit (Dom.Set (LitSet.singleton (LBool true)))
             else if Expr.compare_lit maxa minb < 0 then rlit (Dom.Set (LitSet.singleton (LBool false)))
             else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | (Eq_int_int
          | Eq_rat_rat
          | Eq_mon_mon
          | Eq_dat_dat
          | Eq_dur_dur), [Lit d1; Lit d2] ->
          (match Dom.cleanup d1.v, Dom.cleanup d2.v with
           | Set s, d | d, Set s ->
             if LitSet.cardinal s = 1 then
               if not (Dom.memv (LitSet.choose s) d) then rlit (Dom.Set (LitSet.singleton (LBool false)))
               else match d with
                 | Set s2 when LitSet.equal s s2 ->
                   rlit (Dom.Set (LitSet.singleton (LBool true)))
                 | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
             else rlit (Dom.Set (LitSet.of_list [LBool true; LBool false]))
           | _ -> rlit (Dom.Set (LitSet.of_list [LBool true; LBool false])))
        | _ -> rlit Dom.Any
      )


(** {1 API} *)

let interpret_program :
      'm. decl_ctx -> 'm Ast.expr -> (Uid.MarkedString.info * 'm Ast.expr) list
    =
 fun (ctx : decl_ctx) (e : 'm Ast.expr) :
     (Uid.MarkedString.info * 'm Ast.expr) list ->
  match evaluate_expr ctx env e with
  | (EAbs { tys = [((TStruct s_in, _) as _targs)]; _ }, mark_e) as e -> begin
    (* At this point, the interpreter seeks to execute the scope but does not
       have a way to retrieve input values from the command line. [taus] contain
       the types of the scope arguments. For [context] arguments, we can provide
       an empty thunked term. But for [input] arguments of another type, we
       cannot provide anything so we have to fail. *)
    let taus = StructName.Map.find s_in ctx.ctx_structs in
    let application_term =
      StructField.Map.map
        (fun ty ->
          match Marked.unmark ty with
          | TArrow (ty_in, ty_out) ->
            Expr.make_abs
              [| Var.make "_" |]
              (Bindlib.box (ELit LEmptyError), Expr.with_ty mark_e ty_out)
              [ty_in] (Expr.mark_pos mark_e)
          | _ ->
            Errors.raise_spanned_error (Marked.get_mark ty)
              "This scope needs input arguments to be executed. But the Catala \
               built-in interpreter does not have a way to retrieve input \
               values from the command line, so it cannot execute this scope. \
               Please create another scope thatprovide the input arguments to \
               this one and execute it instead. ")
        taus
    in
    let to_interpret =
      Expr.make_app (Expr.box e)
        [Expr.estruct s_in application_term mark_e]
        (Expr.pos e)
    in
    match Marked.unmark (evaluate_expr ctx env (Expr.unbox to_interpret)) with
    | EStruct { fields; _ } ->
      List.map
        (fun (fld, e) -> StructField.get_info fld, e)
        (StructField.Map.bindings fields)
    | _ ->
      Errors.raise_spanned_error (Expr.pos e)
        "The interpretation of a program should always yield a struct \
         corresponding to the scope variables"
  end
  | _ ->
    Errors.raise_spanned_error (Expr.pos e)
      "The interpreter can only interpret terms starting with functions having \
       thunked arguments"
