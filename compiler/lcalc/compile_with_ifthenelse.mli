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

(** Translation from the default calculus to the lambda calculus. This
    translation relies only on nested [if then else] constructions, without need for option types, monads, built-in [HandleDefault] operators or exceptions (except for fatal cases).

    WARNING: the implemented semantics is slightly different from the normal one, and has not been proved equivalent at this point. In short, exceptions won't propagate outside of immediately nested [Default] blocks, which would normally be the case.
*)

val translate_program : 'm Dcalc.Ast.program -> 'm Ast.program
