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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller.

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Require Export Mach.

Section RELSEM.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s fb sp (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs m)
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      (* Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
      step (State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m)
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b vargs t vres rs' m',
      eval_builtin_args ge rs sp m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff c rs m f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      (* Mem.free m stk 0 f.(fn_stacksize) = Some m' -> *)
      step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m)
  | exec_function_internal:
      forall s fb rs m f m2 m3 rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      let sp := Val.offset_ptr (parent_sp s) (Ptrofs.repr (fn_stacksize f)) in
      (* Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) -> *)
      (* let sp := Vptr stk Ptrofs.zero in *)
      store_stack m (parent_sp s) Tptr f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 (parent_sp s) Tptr f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call ef ge args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res rs ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m,
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).
