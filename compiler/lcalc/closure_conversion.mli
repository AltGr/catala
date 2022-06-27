(* This file is part of the Catala compiler, a specification language for tax
   and social benefits computation rules. Copyright (C) 2022 Inria, contributor:
   Denis Merigoux <denis.merigoux@inria.fr>

   Licensed under the Apache License, Version 2.0 (the "License"); you may not
   use this file except in compliance with the License. You may obtain a copy of
   the License at

   http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations under
   the License. *)

val closure_conversion: Dcalc.Ast.untyped Ast.program -> Dcalc.Ast.untyped Ast.program Bindlib.box
(* TODO: at the moment this interface restricts to untyped AST although a typed
   ast would be accepted, because no effort was yet made to ensure the correct
   propagation of types during the transformation *)
