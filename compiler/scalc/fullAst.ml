(**{[

## surface

  (completely different, skip)
     
## desugared

  type marked_expr = expr Marked.pos
(** The expressions use the {{:https://lepigre.fr/ocaml-bindlib/} Bindlib}
    library, based on higher-order abstract syntax*)

and expr =
*  | ELocation of location
*  | EVar of expr Bindlib.var
*  | EStruct of
      Scopelang.Ast.StructName.t * marked_expr Scopelang.Ast.StructFieldMap.t
*  | EStructAccess of
      marked_expr * Scopelang.Ast.StructFieldName.t * Scopelang.Ast.StructName.t
*  | EEnumInj of
      marked_expr * Scopelang.Ast.EnumConstructor.t * Scopelang.Ast.EnumName.t
*  | EMatch of
      marked_expr
      * Scopelang.Ast.EnumName.t
      * marked_expr Scopelang.Ast.EnumConstructorMap.t
*  | ELit of Dcalc.Ast.lit
*  | EAbs of
      (expr, marked_expr) Bindlib.mbinder * Scopelang.Ast.typ Marked.pos list
*  | EApp of marked_expr * marked_expr list
*  | EOp of Dcalc.Ast.operator
*  | EDefault of marked_expr list * marked_expr * marked_expr
*  | EIfThenElse of marked_expr * marked_expr * marked_expr
*  | EArray of marked_expr list
*  | ErrorOnEmpty of marked_expr

## scopelang

type marked_expr = expr Marked.pos

and expr =
*  | ELocation of location
*  | EVar of expr Bindlib.var
*  | EStruct of StructName.t * marked_expr StructFieldMap.t
*  | EStructAccess of marked_expr * StructFieldName.t * StructName.t
*  | EEnumInj of marked_expr * EnumConstructor.t * EnumName.t
*  | EMatch of marked_expr * EnumName.t * marked_expr EnumConstructorMap.t
*  | ELit of Dcalc.Ast.lit
*  | EAbs of (expr, marked_expr) Bindlib.mbinder * typ Marked.pos list
*  | EApp of marked_expr * marked_expr list
*  | EOp of Dcalc.Ast.operator
*  | EDefault of marked_expr list * marked_expr * marked_expr
*  | EIfThenElse of marked_expr * marked_expr * marked_expr
*  | EArray of marked_expr list
*  | ErrorOnEmpty of marked_expr

## dcalc

type 'm marked_expr = ('m expr, 'm) marked

and 'm expr =
*  | EVar of 'm expr Bindlib.var
*  | ETuple of 'm marked_expr list * StructName.t option
*  | ETupleAccess of
      'm marked_expr * int * StructName.t option * typ Marked.pos list
*  | EInj of 'm marked_expr * int * EnumName.t * typ Marked.pos list
*  | EMatch of 'm marked_expr * 'm marked_expr list * EnumName.t
*  | EArray of 'm marked_expr list
*  | ELit of lit
*  | EAbs of
      (('m expr, 'm marked_expr) Bindlib.mbinder[@opaque]) * typ Marked.pos list
*  | EApp of 'm marked_expr * 'm marked_expr list
*  | EAssert of 'm marked_expr
*  | EOp of operator
*  | EDefault of 'm marked_expr list * 'm marked_expr * 'm marked_expr
*  | EIfThenElse of 'm marked_expr * 'm marked_expr * 'm marked_expr
*  | ErrorOnEmpty of 'm marked_expr


## lcalc

type 'm marked_expr = ('m expr, 'm) D.marked

and 'm expr =
*  | EVar of 'm expr Bindlib.var
*  | ETuple of 'm marked_expr list * D.StructName.t option
      (** The [MarkedString.info] is the former struct field name*)
*  | ETupleAccess of
      'm marked_expr * int * D.StructName.t option * D.typ Marked.pos list
      (** The [MarkedString.info] is the former struct field name *)
*  | EInj of 'm marked_expr * int * D.EnumName.t * D.typ Marked.pos list
      (** The [MarkedString.info] is the former enum case name *)
*  | EMatch of 'm marked_expr * 'm marked_expr list * D.EnumName.t
      (** The [MarkedString.info] is the former enum case name *)
*  | EArray of 'm marked_expr list
*  | ELit of lit
*  | EAbs of ('m expr, 'm marked_expr) Bindlib.mbinder * D.typ Marked.pos list
*  | EApp of 'm marked_expr * 'm marked_expr list
*  | EAssert of 'm marked_expr
*  | EOp of D.operator
*  | EIfThenElse of 'm marked_expr * 'm marked_expr * 'm marked_expr
*  | ERaise of except
*  | ECatch of 'm marked_expr * except * 'm marked_expr

## scalc

type expr =
*  | EVar of LocalName.t
*  | EFunc of TopLevelName.t
*  | EStruct of expr Marked.pos list * D.StructName.t
*  | EStructFieldAccess of expr Marked.pos * D.StructFieldName.t * D.StructName.t
*  | EInj of expr Marked.pos * D.EnumConstructor.t * D.EnumName.t
*  | EArray of expr Marked.pos list
*  | ELit of L.lit
*  | EApp of expr Marked.pos * expr Marked.pos list
*  | EOp of Dcalc.Ast.operator

type stmt =
  | SInnerFuncDef of LocalName.t Marked.pos * func
  | SLocalDecl of LocalName.t Marked.pos * D.typ Marked.pos
  | SLocalDef of LocalName.t Marked.pos * expr Marked.pos
  | STryExcept of block * L.except * block
  | SRaise of L.except
  | SIfThenElse of expr Marked.pos * block * block
  | SSwitch of
      expr Marked.pos
      * D.EnumName.t
      * (block (* Statements corresponding to arm closure body*)
        * (* Variable instantiated with enum payload *) LocalName.t)
        list  (** Each block corresponds to one case of the enum *)
  | SReturn of expr
  | SAssert of expr

                
     
   ]}*)





(* type 'a marked_expr = ('a expr, mark) Marked.t
 * and 'a expr =
 *   | ELit of lit (\* all *\)
 *   | EApp of expr Marked.pos * expr Marked.pos list (\* all *\)
 *   | EOp of operator (\* all *\)
 *   | EArray of 'm marked_expr list (\* all *\)
 *   | ELocation of location (\* desu scope *\)
 *   | EVar of expr Bindlib.var (\* desu scope dcalc lcalc *\)
 *   | EVar of LocalName.t (\* scalc *\)
 *   | EStruct of StructName.t * marked_expr StructFieldMap.t (\* desu scope *\)
 *   | EStructAccess of marked_expr * StructFieldName.t * StructName.t (\* desu scope *\)
 *   | ETuple of 'm marked_expr list * D.StructName.t option (\* dcalc lcalc *\)
 *   | ETupleAccess of 'm marked_expr * int * D.StructName.t option * D.typ Marked.pos list (\* dcalc lcalc *\)
 *   | EStruct of expr Marked.pos list * D.StructName.t (\* scalc *\)
 *   | EStructFieldAccess of expr Marked.pos * D.StructFieldName.t * D.StructName.t (\* scalc *\)
 *   | EEnumInj of marked_expr * EnumConstructor.t * EnumName.t (\* desu scope scalc(!) *\)
 *   | EInj of 'm marked_expr * int * EnumName.t * typ Marked.pos list (\* dcalc lcalc *\)
 *   | EFunc of TopLevelName.t (\* scalc *\)
 *   | EMatch of marked_expr * EnumName.t * marked_expr EnumConstructorMap.t (\* desu scope *\)
 *   | EMatch of 'm marked_expr * 'm marked_expr list * D.EnumName.t (\* dcalc lcalc *\)
 *   | EAbs of (expr, marked_expr) Bindlib.mbinder * typ Marked.pos list (\* desu scope dcalc lcalc *\)
 *   | EAssert of 'm marked_expr (\* dcalc lcalc *\)        
 *   | EIfThenElse of 'm marked_expr * 'm marked_expr * 'm marked_expr (\* desu scope dcalc lcalc *\)
 *   | EDefault of marked_expr list * marked_expr * marked_expr (\* desu scope dcalc *\)
 *   | ErrorOnEmpty of 'm marked_expr (\* desu scope dcalc *\)
 *   | ERaise of except (\* lcalc *\)
 *   | ECatch of 'm marked_expr * except * 'm marked_expr (\* lcalc *\) *)

open Utils

open Dcalc.Ast
open Scopelang.Ast

type except = ConflictError | EmptyError | NoValueProvided | Crash
(* for lcalc *)

module TopLevelName = Uid.Make (Uid.MarkedString) ()
module LocalName = Uid.Make (Uid.MarkedString) ()
(* for scalc *)

type mark


type desugared = [ `Desugared ]
type scopelang = [ `Scopelang ]
type dcalc = [ `Dcalc ]
type lcalc = [ `Lcalc ]
type scalc = [ `Scalc ]

type 'a marked_expr = ('a expr *  mark)
and 'a expr =

  (* Constructors common to all ASTs *)
  | ELit: lit -> 'a expr
  | EApp: 'a marked_expr * 'a marked_expr list -> 'a expr
  | EOp: operator -> 'a expr
  | EArray: 'a marked_expr list -> 'a expr

  (* All but statement calculus *)
  | EVar: 'a expr Bindlib.var -> ([< desugared | scopelang | dcalc | lcalc ] as 'a) expr
  | EAbs: ('a expr, 'a marked_expr) Bindlib.mbinder * typ Marked.pos list -> ([< desugared | scopelang | dcalc | lcalc ] as 'a) expr
  | EIfThenElse: 'a marked_expr * 'a marked_expr * 'a marked_expr -> ([< desugared | scopelang | dcalc | lcalc ] as 'a) expr

  (* Early stages *)
  | ELocation: location -> ([< desugared | scopelang ] as 'a) expr
  | EStruct: StructName.t * 'a marked_expr StructFieldMap.t -> ([< desugared | scopelang ] as 'a) expr
  | EStructAccess: 'a marked_expr * StructFieldName.t * StructName.t -> ([< desugared | scopelang ] as 'a) expr
  | EEnumInj: 'a marked_expr * EnumConstructor.t * EnumName.t -> ([< desugared | scopelang ] as 'a) expr
  | EMatchS: 'a marked_expr * EnumName.t * 'a marked_expr EnumConstructorMap.t -> ([< desugared | scopelang ] as 'a) expr

  (* Default terms *)
  | EDefault: 'a marked_expr list * 'a marked_expr * 'a marked_expr -> ([< desugared | scopelang | dcalc ] as 'a) expr
  | ErrorOnEmpty: 'a marked_expr -> ([< desugared | scopelang | dcalc ] as 'a) expr

  (* Lambda-like *)
  | ETuple: 'a marked_expr list * StructName.t option -> ([< dcalc | lcalc ] as 'a) expr
  | ETupleAccess: 'a marked_expr * int * StructName.t option * typ Marked.pos list -> ([< dcalc | lcalc ] as 'a) expr
  | EInj: 'a marked_expr * int * EnumName.t * typ Marked.pos list -> ([< dcalc | lcalc ] as 'a) expr
  | EMatchL: 'a marked_expr * 'a marked_expr list * EnumName.t -> ([< dcalc | lcalc ] as 'a) expr
  | EAssert: 'a marked_expr -> ([< dcalc | lcalc ] as 'a) expr

  (* Lambda calculus with exceptions *)
  | ERaise: except -> (lcalc as 'a) expr
  | ECatch: 'a marked_expr * except * 'a marked_expr -> (lcalc as 'a) expr

  (* Statement calculus *)
  | ESVar: LocalName.t -> (scalc as 'a) expr
  | ESStruct: 'a marked_expr list * StructName.t -> (scalc as 'a) expr
  | ESStructFieldAccess: 'a marked_expr * StructFieldName.t * StructName.t -> (scalc as 'a) expr
  | ESInj: 'a marked_expr * EnumConstructor.t * EnumName.t -> (scalc as 'a) expr
  | ESFunc: TopLevelName.t -> (scalc as 'a) expr
