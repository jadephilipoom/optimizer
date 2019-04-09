Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Require Import Optimizer.Util.Tactics.
Require Import Optimizer.Util.ZUtil.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.ProofOfConcept.Candidates.
Require Import Optimizer.ProofOfConcept.CostModel.
Require Import Optimizer.ProofOfConcept.Flags.
Require Import Optimizer.ProofOfConcept.Instructions.
Require Import Optimizer.ProofOfConcept.Registers.
Require Import Optimizer.ProofOfConcept.Maps.

Import Machine. Import Registers. Import Instructions.
Require Import Optimizer.ProofOfConcept.Glue. (* Do this last so as not to override notations *)

Import ListNotations.
Local Open Scope Z_scope.

Definition examples : list program :=
  [
    (Ret r0); (* simplest program *)

      (* move value in r3 to r2 and return it *)
      (Instr MOV64 r2 (%r3 :: nil) (Ret r2));
      
      (* r0 + r1 with 32-bit add, result in r0 *)
      (Instr ADD32 r0 (%r0 :: %r1 :: nil) (Ret r0));

      (* r0 + r1 with 32-bit add, result in r2 (which is oversized) *)
      (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Ret r2));

      (* r0 + r1 with 64-bit add, result in r2 *)
      (Instr ADD64 r2 (%r0 :: %r1 :: nil) (Ret r2));

      (* (r0 + r1) >> 1 with 32-bit add, result in r2 *)
      (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2)));

      (* (r0 + r1) >> 1 with 64-bit add, result in r2 *)
      (Instr ADD64 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2)))
  ].

Lemma examples_valid : Forall valid examples.
Proof.
  repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
    try break_match; try lia.
Qed.

Hint Unfold
     Machine.equivalent Machine.exec 
     CostModel.optimal CostModel.cost
     Instructions.instr_cost Instructions.precondition.
Ltac simplify := autounfold; cbn [size value spec arg_value].

(* prove sum using 32- and 64- bit adds give the same result *)
Section SumEquiv.
  Definition sum :=
    Eval compute in (nth_default (Ret r0) examples 5). (* ADD32 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
  Definition sum' :=
    Eval compute in (nth_default (Ret r0) examples 6). (* ADD64 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
  Hint Unfold sum sum'.
  
  Lemma sums_equiv : sum == sum'.
  Proof.
    repeat match goal with
           | _ => progress (intros; autounfold; simplify)
           | _ => progress autorewrite with push_map push_mapt push_nth_default
           | _ => progress MachineProofs.pose_valid_context_range
           | |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia
           end.
    reflexivity.
  Qed.
End SumEquiv.

(* Prove that programs are optimal *)
Section Optimal.
  Definition simple_sum :=  (Instr ADD32 r0 (%r0 :: %r1 :: nil) (Ret r0)).
  (* Eval cbv [simple_sum] in simple_sum. (* ADD32 r2 r0 r1; Ret r2 *) *)
  Hint Unfold simple_sum.

  Lemma simple_sum_valid : valid simple_sum.
  Proof.
    repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
      try break_match; try lia.
  Qed.
  Lemma simple_sum_optimal : optimal simple_sum.
  Proof.
    apply (All.optimal_limited_domain_equiv simple_sum simple_sum_valid); cbn.
    repeat match goal with
           | |- Forall _ _ => econstructor
           | |- forall x, ?rep _ x -> ~ _ == x =>
             let P := fresh "p" in
             intro p; inversion 1
           | H : Enumerators.to_abstract ?x = _ |- _ =>
             destruct x; cbn [Enumerators.to_abstract] in H; try congruence; [ ]
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
           end.
    { cbv [simple_sum equivalent]; intro.
      (* TODO: use some test vectors to prove these two are not equivalent. *)
      admit. }
    { cbv [simple_sum equivalent]; intro.
      (* TODO: use some test vectors to prove these two are not equivalent. *)
      admit. }
  Admitted.

  Definition sum_shift :=
    (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2))).
  (* Eval cbv [sum_shift] in sum_shift. (* ADD32 %r2 %r0 %r1; SHR64 %r2 %r2 $1; Ret r2 *) *)
  Hint Unfold sum_shift.

  Lemma sum_shift_valid : valid sum_shift.
  Proof.
    repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
      try break_match; try lia.
  Qed.
  Lemma sum_shift_optimal : optimal sum_shift.
  Proof.
    apply (All.optimal_limited_domain_equiv _ sum_shift_valid); cbn.
    repeat match goal with
           | |- Forall _ _ => econstructor
           | |- forall x, ?rep _ x -> ~ _ == x =>
             let P := fresh "p" in
             intro p; inversion 1
           | H : Enumerators.to_abstract ?x = _ |- _ =>
             destruct x; cbn [Enumerators.to_abstract] in H; try congruence; [ ]
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
           end.
    (* 13 subgoals; will want to refine more *)
  Admitted.
End Optimal.