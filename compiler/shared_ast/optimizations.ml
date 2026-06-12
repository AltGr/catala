(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2022 Inria,
   contributors: Alain Delaët <alain.delaet--tixeuil@inria.fr>, Denis Merigoux
   <denis.merigoux@inria.fr>

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

type 'e down_acc = { decl_ctx : decl_ctx }

type 'e up_acc = {
  free_vars: ('e, int) Var.Map.t; (* counts occurences *)
  size: int;
  is_pure: bool;
}

let uacc_empty = {
  free_vars = Var.Map.empty;
  size = 0;
  is_pure = true;
}

let uacc_merge uacc1 uacc2 =
  {
    free_vars = Var.Map.union (fun _ n1 n2 -> Some (n1 + n2)) uacc1.free_vars uacc2.free_vars;
    size = uacc1.size + uacc2.size;
    is_pure = uacc1.is_pure && uacc2.is_pure;
  }

let uacc_occur uacc v = match Var.Map.find_opt v uacc.free_vars with
  | Some n -> n
  | None -> 0

let box uacc (e, m) =
  Bindlib.box_apply (fun e -> uacc, (e, m)) e, m

let literal_bool = function
  | ELit (LBool b), _
  | EAppOp { op = Log _, _; args = [(ELit (LBool b), _)]; _ }, _ ->
    Some b
  | _ -> None


(* beta reduction when variables not used, and for variable aliases and
   literals *)
let rec simplified_apply dacc f args tys m =
  let uargs =
    args |>
    List.map (fun e -> let arg, _ = optimize_expr dacc e in arg) |>
    Bindlib.box_list |>
    Bindlib.box_apply (fun uargs ->
        let uacc_args, args = List.split uargs in
        let uacc_args = List.fold_left uacc_merge uacc_empty uacc_args in
        uacc_args, args)
  in
  match f with
  | EAbs { binder; tys; pos }, _ ->
    (* This only applies to literal lambdas (before optimisations) at the
       moment. A real optimisation pass would handle inlining of named functions
       with some heuristics. *)
    let vars, body = Bindlib.unmbind binder in
    let ubody, _body_m = optimize_expr dacc body in
    let ubinder = Bindlib.bind_mvar vars ubody in (* see [optimize_binder] *)
    Bindlib.box_apply2 (fun ubinder (uacc_args, args) ->
        let vars, (uacc_body, _body) = Bindlib.unmbind ubinder in
        let uacc_f = {
          is_pure = true;
          size = uacc_body.size + 1;
          free_vars = Array.fold_left (fun vars v -> Var.Map.remove v vars) uacc_body.free_vars vars;
        } in
        let uacc = uacc_merge uacc_f uacc_args in
        match args, uacc_args.is_pure with
        | [(EAbs { tys = (TClosureEnv, _) :: _; _ }, _)], _
        (* Never inline lifted closures *)
        | _, false
          (* Do not inline impure expressions *)
          ->
          let binder = Bindlib.mbinder_compose ubinder snd in
          let f = EAbs { binder; tys; pos }, m in
          uacc, (EApp { f; args; tys }, m)
        | _ when
            List.for_all2 (fun v arg ->
                (match arg with (EVar _ | ELit _), _ -> true | _ -> false) ||
                (uacc_occur uacc_body v <= 1)
                (* we could also inline pure args with multiple occurences, under some size
                   threshold *))
              (Array.to_list vars) args
          -> (* Inline all function arguments *)
          let uacc = { uacc with
                       is_pure = uacc_args.is_pure && uacc_body.is_pure;
                       size = uacc_body.size + uacc_args.size -
                              Array.fold_left (fun n v ->
                                  n + uacc_occur uacc_body v)
                                0 vars; }
          in
          uacc, Bindlib.msubst binder (Array.of_seq (Seq.map Mark.remove (List.to_seq args)))
            (* We might want to run another optimisation round here ? *)
        | _ ->
          let binder = Bindlib.mbinder_compose ubinder snd in
          let f = EAbs { binder; tys; pos }, m in
          uacc, (EApp { f; args; tys }, m)
    )
    ubinder
    uargs,
    m
  | _ ->
    let uf, _ = optimize_expr dacc f in
    Bindlib.box_apply2 (fun (uacc_f, f) (uacc_args, args) ->
        uacc_merge uacc_f uacc_args, (EApp { f; args; tys }, m))
    uf
    uargs,
    m

and simplified_ifthenelse dacc cond etrue efalse m =
  if Expr.equal etrue efalse then Mark.remove etrue
  else
    match literal_bool etrue, literal_bool efalse with
    | Some true, Some false -> Mark.remove cond
    | Some false, Some true ->
      EAppOp
        {
          op = Not, Expr.mark_pos m;
          tys = [TLit TBool, Expr.mark_pos m];
          args = [cond];
        }
    | Some true, Some true | Some false, Some false -> Mark.remove etrue
    | _ -> (
      match literal_bool cond with
      | Some true -> Mark.remove etrue
      | Some false -> Mark.remove efalse
      | None -> EIfThenElse { cond; etrue; efalse })

(* builds a [EMatch] term, flattening nested matches/if-then-else: the matching
   arg branching are explored, and if they all lead to enum constructor
   literals, the surrounding match cases are inlined. Code duplication is
   detected and aborts the inlining. *)
and simplified_match dacc enum_name match_arg cases mark =
  let max_duplicate_inlining_size = 3 in
  let allow_duplicate_inlining_cases =
    EnumConstructor.Map.fold
      (fun cons f acc ->
        if Expr.size f <= max_duplicate_inlining_size then
          EnumConstructor.Set.add cons acc
        else acc)
      cases EnumConstructor.Set.empty
  in
  let app_cases cons e =
    simplified_apply
      (EnumConstructor.Map.find cons cases)
      [e]
      [Expr.maybe_ty (Mark.get e)]
  in
  let ret_ty = Expr.maybe_ty mark in
  let rec aux seen_constrs = function
    | EInj { cons; e; _ }, m ->
      if EnumConstructor.Set.mem cons seen_constrs then raise Exit;
      (* Abort inlining to avoid code duplication *)
      let seen_constrs =
        if EnumConstructor.Set.mem cons allow_duplicate_inlining_cases then
          seen_constrs
        else EnumConstructor.Set.add cons seen_constrs
      in
      seen_constrs, (app_cases cons e, Expr.with_ty m ret_ty)
    | EMatch ({ cases; _ } as ematch), m ->
      let seen_constrs, cases =
        EnumConstructor.Map.fold
          (fun cons case (seen_constrs, acc) ->
            match case with
            | EAbs ({ binder; _ } as eabs), m ->
              let vars, body = Bindlib.unmbind binder in
              let seen_constrs, body = aux seen_constrs body in
              let binder = Bindlib.unbox (Expr.bind vars (Expr.rebox body)) in
              let m =
                Expr.map_ty
                  (function
                    | TArrow (args, _), pos -> TArrow (args, ret_ty), pos
                    | (TVar _, _) as t -> t
                    | _ -> assert false)
                  m
              in
              ( seen_constrs,
                EnumConstructor.Map.add cons (EAbs { eabs with binder }, m) acc
              )
            | _ -> assert false)
          cases
          (seen_constrs, EnumConstructor.Map.empty)
      in
      seen_constrs, (EMatch { ematch with cases }, Expr.with_ty m ret_ty)
    | EIfThenElse { cond; etrue; efalse }, m ->
      let seen_constrs, etrue = aux seen_constrs etrue in
      let seen_constrs, efalse = aux seen_constrs efalse in
      let mark = Expr.with_ty m ret_ty in
      seen_constrs, (simplified_ifthenelse cond etrue efalse mark, mark)
    | _ -> raise Exit
  in
  try
    let _seen_contrs, e = aux EnumConstructor.Set.empty match_arg in
    Mark.remove e
  with Exit ->
    (* Optimisation was aborted due a non-terminal or code duplication *)
    EMatch { e = match_arg; cases; name = enum_name }

and optimize_binder dacc binder =
  let vars, body = Bindlib.unmbind binder in
  let ubody, _m = optimize_expr dacc body in
  let ubinder = Bindlib.bind_mvar vars ubody in
  Bindlib.box_apply (fun ubinder ->
      (* Here we recover the body without the upwards accumulator using
         [mbinder_compose], and need in parallel to unmbind right away to
         retrieve the upwards acc, from which we strip the local variables. This
         is the least wasteful way to proceed that I could figure. *)
      let binder = Bindlib.mbinder_compose ubinder snd in
      let vars, (uacc_body, _) = Bindlib.unmbind ubinder in
      let uacc = {
        free_vars = Array.fold_left (fun vars v -> Var.Map.remove v vars) uacc_body.free_vars vars;
        size = uacc_body.size + 1;
        is_pure = true;
      } in
      uacc, binder
    )
    ubinder

and optimize_expr : type a b.
    'e down_acc ->
    (((a, b) dcalc_lcalc, 'm) gexpr as 'e) ->
    ('e up_acc *
     ((a, b) dcalc_lcalc, 'm) gexpr)
      Bindlib.box * 'm mark =
 fun dacc (e, m) ->
 match e with
 | EAppOp { op = Not, _; args = [(ELit (LBool b), _)]; _ } ->
   (* reduction of logical not *)
   box { uacc_empty with size = 1 } (Expr.elit (LBool (not b)) m)
 | EAppOp { op = Or, _ as op; args = [e1; e2]; tys } ->
   let u1, _ = optimize_expr dacc e1 in
   let u2, _ = optimize_expr dacc e2 in
   Bindlib.box_apply2 (fun (uacc1, e1) (uacc2, e2) ->
       match e1 with
       | ELit (LBool false), _ -> uacc2, e2
       | ELit (LBool true), _ when uacc2.is_pure -> uacc1, e1
       | e1 -> match e2 with
         | ELit (LBool false), _ -> uacc1, e1
         | ELit (LBool true), _ when uacc1.is_pure -> uacc2, e2
         | e2 -> uacc_merge uacc1 uacc2, (EAppOp { op; args = [e1; e2]; tys }, m))
     u1 u2,
   m
 | EAppOp { op = And, _ as op; args = [e1; e2]; tys } ->
   let u1, _ = optimize_expr dacc e1 in
   let u2, _ = optimize_expr dacc e2 in
   Bindlib.box_apply2 (fun (uacc1, e1) (uacc2, e2) ->
       match e1 with
       | ELit (LBool true), _ -> uacc2, e2
       | ELit (LBool false), _ when uacc2.is_pure -> uacc1, e1
       | e1 -> match e2 with
         | ELit (LBool true), _ -> uacc1, e1
         | ELit (LBool false), _ when uacc1.is_pure -> uacc2, e2
         | e2 -> uacc_merge uacc1 uacc2, (EAppOp { op; args = [e1; e2]; tys }, m))
     u1 u2,
   m
 | EMatch { name; e; cases } ->
   simplified_match dacc uacc name e cases mark
 | EApp { f; args; tys } -> simplified_apply vars f args tys
 | EStructAccess { name; field; e = EStruct { name = name1; fields }, _ }
   when StructName.equal name name1 ->
   vars, Mark.remove (StructField.Map.find field fields)
 | EErrorOnEmpty (EPureDefault (e, _), _) -> e
 | EDefault { excepts; just; cons } -> (
     (* TODO: mechanically prove each of these optimizations correct *)
     let excepts =
       List.filter (fun except -> Mark.remove except <> EEmpty) excepts
       (* we can discard the exceptions that are always empty error *)
     in
     let value_except_count =
       List.fold_left
         (fun nb except -> if Expr.is_value except then nb + 1 else nb)
         0 excepts
     in
     if value_except_count > 1 then
       (* at this point we know a conflict error will be triggered so we just
          feed the expression to the interpreter that will print the beautiful
          right error message *)
       let (_ : _ gexpr) =
         Interpreter.evaluate_expr ctx.decl_ctx `En
           (* Default language to English, no errors should be raised normally
              so we don't care *)
           e
       in
       assert false
     else
       match excepts, just with
       | [(EDefault { excepts = []; just = ELit (LBool true), _; cons }, _)], _
         ->
         (* No exceptions with condition [true] *)
         vars, Mark.remove cons
       | [], cond -> simplified_ifthenelse cond cons (EEmpty, mark) mark
       | ( [except],
           ( ( ELit (LBool false)
             | EAppOp { op = Log _, _; args = [(ELit (LBool false), _)]; _ } ),
             _ ) ) ->
         (* Single exception and condition false *)
         Mark.remove except
       | excepts, just -> EDefault { excepts; just; cons })
 | EIfThenElse { cond; etrue; efalse } ->
   simplified_ifthenelse cond etrue efalse mark
 | EAppOp { op = Op.Fold, _; args = [_f; init; (EArray [], _)]; _ } ->
   (*reduces a fold with an empty list *)
   Mark.remove init
 | EAppOp
     {
       op = (Map, _) as op;
       args =
         [
           f1;
           ( EAppOp
               {
                 op = Map, _;
                 args = [f2; ls];
                 tys = [_; ((TArray xty, _) as lsty)];
               },
             m2 );
         ];
       tys = [_; (TArray yty, _)];
     } ->
   (* map f (map g l) => map (f o g) l *)
   let fg =
     let v =
       Var.make
         (match f2 with
          | EAbs { binder; _ }, _ -> (Bindlib.mbinder_names binder).(0)
          | _ -> "x")
     in
     let mty m =
       Expr.map_ty (function TArray ty, _ -> ty | _, pos -> Type.any pos) m
     in
     let x = Expr.evar v (mty (Mark.get ls)) in
     Expr.make_ghost_abs [v]
       (Expr.eapp ~f:(Expr.box f1)
          ~args:[Expr.eapp ~f:(Expr.box f2) ~args:[x] ~tys:[xty] (mty m2)]
          ~tys:[yty] (mty mark))
       [xty] (Expr.pos e)
   in
   let fg = optimize_expr ctx (Expr.unbox fg) in
   let mapl =
     Expr.eappop ~op
       ~args:[fg; Expr.box ls]
       ~tys:[Expr.maybe_ty (Mark.get fg); lsty]
       mark
   in
   Mark.remove (Expr.unbox mapl)
 | EAppOp
     {
       op = Map, _;
       args =
         [
           f1;
           ( EAppOp
               {
                 op = (Map2, _) as op;
                 args = [f2; ls1; ls2];
                 tys =
                   [
                     _;
                     ((TArray x1ty, _) as ls1ty);
                     ((TArray x2ty, _) as ls2ty);
                   ];
               },
             m2 );
         ];
       tys = [_; (TArray yty, _)];
     } ->
   (* map f (map2 g l1 l2) => map2 (f o g) l1 l2 *)
   let fg =
     let v1, v2 =
       match f2 with
       | EAbs { binder; _ }, _ ->
         let names = Bindlib.mbinder_names binder in
         Var.make names.(0), Var.make names.(1)
       | _ -> Var.make "x", Var.make "y"
     in
     let mty m =
       Expr.map_ty (function TArray ty, _ -> ty | _, pos -> Type.any pos) m
     in
     let x1 = Expr.evar v1 (mty (Mark.get ls1)) in
     let x2 = Expr.evar v2 (mty (Mark.get ls2)) in
     Expr.make_ghost_abs [v1; v2]
       (Expr.eapp ~f:(Expr.box f1)
          ~args:
            [
              Expr.eapp ~f:(Expr.box f2) ~args:[x1; x2] ~tys:[x1ty; x2ty]
                (mty m2);
            ]
          ~tys:[yty] (mty mark))
       [x1ty; x2ty] (Expr.pos e)
   in
   let fg = optimize_expr ctx (Expr.unbox fg) in
   let mapl =
     Expr.eappop ~op
       ~args:[fg; Expr.box ls1; Expr.box ls2]
       ~tys:[Expr.maybe_ty (Mark.get fg); ls1ty; ls2ty]
       mark
   in
   Mark.remove (Expr.unbox mapl)
 | EAppOp
     {
       op = Op.Fold, _;
       args = [f; init; (EArray [e'], _)];
       tys = [_; tinit; (TArray tx, _)];
     } ->
   (* reduces a fold with one element *)
   EApp { f; args = [init; e']; tys = [tinit; tx] }
 | ETuple ((ETupleAccess { e; index = 0; _ }, _) :: el)
   when List.for_all Fun.id
       (List.mapi
          (fun i -> function
             | ETupleAccess { e = en; index; _ }, _ ->
               index = i + 1 && Expr.equal en e
             | _ -> false)
          el) ->
   (* identity tuple reconstruction *)
   Mark.remove e
 | e -> e

let optimize_expr :
    'm.
    decl_ctx ->
    (('a, 'b) dcalc_lcalc, 'm) gexpr ->
    (('a, 'b) dcalc_lcalc, 'm) boxed_gexpr =
 fun (decl_ctx : decl_ctx) (e : (('a, 'b) dcalc_lcalc, 'm) gexpr) ->
  optimize_expr { decl_ctx } e

let optimize_program (p : 'm program) : 'm program =
  Program.map_exprs ~f:(optimize_expr p.decl_ctx) ~varf:(fun v -> v) p

let test_iota_reduction_1 () =
  let x = Var.make "x" in
  let enumT = EnumName.fresh [] ("t", Pos.void) in
  let consA = EnumConstructor.fresh ("A", Pos.void) in
  let consB = EnumConstructor.fresh ("B", Pos.void) in
  let consC = EnumConstructor.fresh ("C", Pos.void) in
  let consD = EnumConstructor.fresh ("D", Pos.void) in
  let nomark = Untyped { pos = Pos.void } in
  let injA = Expr.einj ~e:(Expr.evar x nomark) ~cons:consA ~name:enumT nomark in
  let injC = Expr.einj ~e:(Expr.evar x nomark) ~cons:consC ~name:enumT nomark in
  let injD = Expr.einj ~e:(Expr.evar x nomark) ~cons:consD ~name:enumT nomark in
  let cases : ('a, 't) boxed_gexpr EnumConstructor.Map.t =
    EnumConstructor.Map.of_list
      [
        ( consA,
          Expr.eabs_ghost (Expr.bind [| x |] injC) [Type.any Pos.void] nomark );
        ( consB,
          Expr.eabs_ghost (Expr.bind [| x |] injD) [Type.any Pos.void] nomark );
      ]
  in
  let matchA = Expr.ematch ~e:injA ~name:enumT ~cases nomark in
  Alcotest.(check string)
    "same string"
    begin[@ocamlformat "disable"]
      "before=match A x with\n\
      \       | A x → C x\n\
      \       | B x → D x\n\
       after=C x"
    end
    (Format.asprintf "before=%a\nafter=%a" Expr.format (Expr.unbox matchA)
       Expr.format
       (Expr.unbox (optimize_expr Program.empty_ctx (Expr.unbox matchA))))

let cases_of_list l : ('a, 't) boxed_gexpr EnumConstructor.Map.t =
  EnumConstructor.Map.of_list
  @@ ListLabels.map l ~f:(fun (cons, f) ->
      let var = Var.make "x" in
      ( cons,
        Expr.eabs_ghost
          (Expr.bind [| var |] (f var))
          [Type.any Pos.void]
          (Untyped { pos = Pos.void }) ))

let test_iota_reduction_2 () =
  let enumT = EnumName.fresh [] ("t", Pos.void) in
  let consA = EnumConstructor.fresh ("A", Pos.void) in
  let consB = EnumConstructor.fresh ("B", Pos.void) in
  let consC = EnumConstructor.fresh ("C", Pos.void) in
  let consD = EnumConstructor.fresh ("D", Pos.void) in

  let nomark = Untyped { pos = Pos.void } in

  let num n = Expr.elit (LInt (Catala_runtime.integer_of_int n)) nomark in

  let injAe e = Expr.einj ~e ~cons:consA ~name:enumT nomark in
  let injBe e = Expr.einj ~e ~cons:consB ~name:enumT nomark in
  let injCe e = Expr.einj ~e ~cons:consC ~name:enumT nomark in
  let injDe e = Expr.einj ~e ~cons:consD ~name:enumT nomark in

  (* let injA x = injAe (Expr.evar x nomark) in *)
  let injB x = injBe (Expr.evar x nomark) in
  let injC x = injCe (Expr.evar x nomark) in
  let injD x = injDe (Expr.evar x nomark) in

  let matchA =
    Expr.ematch
      ~e:
        (Expr.ematch ~e:(num 1) ~name:enumT
           ~cases:
             (cases_of_list
                [
                  (consB, fun x -> injBe (injB x));
                  (consA, fun _x -> injAe (num 20));
                ])
           nomark)
      ~name:enumT
      ~cases:(cases_of_list [consA, injC; consB, injD])
      nomark
  in
  Alcotest.(check string)
    "same string "
    begin[@ocamlformat "disable"]
      "before=match (match 1 with\n\
      \              | A x → A 20\n\
      \              | B x → B (B x)) with\n\
      \       | A x → C x\n\
      \       | B x → D x\n\
       after=match 1 with\n\
      \      | A x → C 20\n\
      \      | B x → D (B x)\n"
    end
    (Format.asprintf "before=@[%a@]@.after=%a@." Expr.format (Expr.unbox matchA)
       Expr.format
       (Expr.unbox (optimize_expr Program.empty_ctx (Expr.unbox matchA))))
