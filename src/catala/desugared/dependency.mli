(* This file is part of the Catala compiler, a specification language for tax and social benefits
   computation rules. Copyright (C) 2020 Inria, contributor: Nicolas Chataing
   <nicolas.chataing@ens.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
   in compliance with the License. You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software distributed under the License
   is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
   or implied. See the License for the specific language governing permissions and limitations under
   the License. *)

(** Scope dependencies computations using {{:http://ocamlgraph.lri.fr/} OCamlgraph} *)

open Utils

(** {1 Scope variables dependency graph} *)

(** {2 Graph declaration} *)

(** Vertices: scope variables or subscopes.

    The vertices of the scope dependency graph are either :

    - the variables of the scope ;
    - the subscopes of the scope.

    Indeed, during interpretation, subscopes are executed atomically. *)

module Vertex : sig
  type t = Var of Scopelang.Ast.ScopeVar.t | SubScope of Scopelang.Ast.SubScopeName.t

  val format_t : Format.formatter -> t -> unit

  include Graph.Sig.COMPARABLE with type t := t
end

module Edge : Graph.Sig.ORDERED_TYPE_DFT with type t = Pos.t
(** On the edges, the label is the position of the expression responsible for the use of the
    variable. In the graph, [x -> y] if [x] is used in the definition of [y].*)

(** Module of the graph, provided by OCamlGraph *)
module ScopeDependencies : Graph.Sig.P with type V.t = Vertex.t and type E.label = Edge.t

(** Module of the topological traversal of the graph, provided by OCamlGraph *)
module TopologicalTraversal : sig
  val fold : (Vertex.t -> 'a -> 'a) -> ScopeDependencies.t -> 'a -> 'a

  val iter : (Vertex.t -> unit) -> ScopeDependencies.t -> unit
end

(** Tarjan's stongly connected components algorithm, provided by OCamlGraph *)
module SCC : sig
  val scc : ScopeDependencies.t -> int * (Vertex.t -> int)

  val scc_array : ScopeDependencies.t -> Vertex.t list array

  val scc_list : ScopeDependencies.t -> Vertex.t list list
end

(** {2 Graph computations} *)

(** Returns an ordering of the scope variables and subscope compatible with the dependencies of the
    computation *)

val correct_computation_ordering : ScopeDependencies.t -> Vertex.t list
(** Returns an ordering of the scope variables and subscope compatible with the dependencies of the
    computation *)

val check_for_cycle : Ast.scope -> ScopeDependencies.t -> unit
(** Outputs an error in case of cycles. *)

val build_scope_dependencies : Ast.scope -> ScopeDependencies.t
(** Builds the dependency graph of a particular scope *)

(** {1 Exceptions dependency graph} *)

module ExceptionsDependencies : Graph.Sig.P with type V.t = Ast.RuleName.t and type E.label = Edge.t

module ExceptionsSCC : sig
  val scc : ExceptionsDependencies.t -> int * (Ast.RuleName.t -> int)

  val scc_array : ExceptionsDependencies.t -> Ast.RuleName.t list array

  val scc_list : ExceptionsDependencies.t -> Ast.RuleName.t list list
end

val build_exceptions_graph : Ast.rule Ast.RuleMap.t -> Ast.ScopeDef.t -> ExceptionsDependencies.t

val check_for_exception_cycle : ExceptionsDependencies.t -> unit