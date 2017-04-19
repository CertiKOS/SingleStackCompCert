(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Layout of activation records; translation from Linear to Mach. *)

Require Import Coqlib Errors.
Require Import Integers AST.
Require Import Op Locations Linear MachSingleStack.
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Export Stacking.

Local Open Scope string_scope.

(** PW: We align the size of the frame to 8 so that alignment properties that
  held in the multiple stack blocks framework, still hold now. More precisely,
  we want that [shift_offset spofs (align ofs al) = align (shift_offset spofs
  ofs) al], where [al] is 4 or 8. *)

Definition transf_function (f: Linear.function) : res Mach.function :=
  let fe := make_env (function_bounds f) in
  if negb (wt_function f) then
    Error (msg "Ill-formed Linear code")
  else if zlt Ptrofs.max_unsigned fe.(fe_size) then
    Error (msg "Too many spilled variables, stack size exceeded")
  else
    OK (Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         (align (fe_size fe) 8)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr))).

Definition transf_fundef (f: Linear.fundef) : res Mach.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Linear.program) : res Mach.program :=
  transform_partial_program transf_fundef p.
