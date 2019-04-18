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
     Optimality.optimal CostModel.cost
     Instructions.instr_cost Instructions.precondition.
Ltac simplify := autounfold; cbn [size value spec arg_value].

(* prove sum using 32- and 64- bit adds give the same result *)
Section SumEquiv.
  Definition sum :=
    Eval cbv [nth_default nth_error examples] in (nth_default (Ret r0) examples 5). (* ADD32 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
  Definition sum' :=
    Eval cbv [nth_default nth_error examples] in (nth_default (Ret r0) examples 6). (* ADD64 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
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

  Ltac optimal_cases :=
    repeat match goal with
           | |- Forall _ _ => econstructor
           | |- forall x, ?rep _ x -> _ -> ~ _ == x =>
             let P := fresh "p" in
             intro p; inversion 1
           | H : Enumerators.to_abstract ?x = _ |- _ =>
             destruct x; cbn [Enumerators.to_abstract] in H; try congruence; [ ]
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
           end.
  Ltac destruct_args :=
    repeat match goal with
           | Hv : valid _ |- _ =>
             inversion Hv; subst; clear Hv
           | H : System.precondition _ _ ?args |- _ =>
             apply precondition_length_args in H;
             cbn [num_source_regs] in H;
             repeat (destruct args as [|? args]; distr_length; [ ])
           end.
  Ltac test cases :=
    match goal with |- ~ (equivalent _ _) => idtac end;
    let tests := fresh "tests" in
    set (tests:=cases); cbv in tests;
    let Hequiv := fresh in
    cbv [equivalent]; intro Hequiv;
    repeat match goal with
           | tests := nil |- _ => clear tests
           | tests := ?ctx :: ?tests' |- _ =>
                      let H := fresh in
                      let Hvalid := fresh in
                      assert (valid_context ctx) as Hvalid by
                            (cbv [valid_context]; destruct 0; cbn; lia);
                      pose proof (Hequiv ctx (empty false) Hvalid) as H;
                      clear Hvalid tests;
                      set (tests:=tests');
                      repeat progress (cbv [arg_value Maps.RegMaps.get] in H; cbn in H)
           end.

  
  Definition simple_sum :=  (Instr ADD32 r0 (%r0 :: %r1 :: nil) (Ret r0)).
  (* Eval cbv [simple_sum] in simple_sum. (* ADD32 r2 r0 r1; Ret r2 *) *)
  Hint Unfold simple_sum.

  Lemma simple_sum_valid : valid simple_sum.
  Proof.
    repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
      try break_match; try lia.
  Qed.
  Definition simple_sum_tests : list (map register Z) :=
    [
      (update (update (empty 0) r0 0) r1 1);
      (update (update (empty 0) r0 1) r1 0);
      (update (update (empty 0) r0 1) r1 1)
    ].
  Lemma simple_sum_optimal : optimal simple_sum.
  Proof.
    apply (All.optimal_limited_domain_equiv simple_sum simple_sum_valid); cbn.
    optimal_cases; cbv [simple_sum]; intros.
    { test simple_sum_tests.
      break_match; lia. }
    { destruct_args.
      test simple_sum_tests.
      repeat (break_match; try lia). }
  Qed.

  Definition sum_shift :=
    (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2))).
  (* Eval cbv [sum_shift] in sum_shift. (* ADD32 %r2 %r0 %r1; SHR64 %r2 %r2 $1; Ret r2 *) *)
  Hint Unfold sum_shift.

  Definition reg_eqb (ra rb : register) : bool.
    pose rb. pose ra.
    destruct ra, rb;
      try match goal with
          | ra := ?r, rb := ?r |- _ => apply true
          end; apply false.
  Defined.
  Lemma reg_eq_dec_to_eqb A (t f : A) ra rb :
    (if (reg_eq_dec ra rb) then t else f) =
    (if (reg_eqb ra rb) then t else f).
  Proof. destruct ra, rb; cbn; congruence. Qed.

  Lemma sum_shift_valid : valid sum_shift.
  Proof.
    repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
      try break_match; try lia.
  Qed.
  Lemma sum_shift_optimal : optimal sum_shift.
  Proof.
    apply (All.optimal_limited_domain_equiv _ sum_shift_valid); cbn.
    optimal_cases; cbv [simple_sum]; intros.
    all:destruct_args.
    Time all:test simple_sum_tests. (* 49.641s *)

    Ltac innermost_mod_small t :=
      match t with
      | context [?a mod ?b] =>
        match goal with
          | _ => innermost_mod_small a
          | _ => constr:((a,b))
        end
      end.
    Ltac solve_case :=
      repeat match goal with
             | _ => progress subst
             | _ => break_match; try lia
             | _ => progress change (Z.shiftr 0 0) with 0 in *
             | _ => progress change (Z.shiftr 1 0) with 1 in *
             | _ => progress change (Z.shiftr 0 1) with 0 in *
             | _ => progress change (Z.shiftl 0 0) with 0 in *
             | _ => progress change (Z.shiftl 1 0) with 1 in *
             | _ => progress change (Z.shiftl 0 1) with 0 in *
             | H : _ = ?t |- _ =>
               match innermost_mod_small t with
               | (?a,?b) =>
                 rewrite (Z.mod_small a b) in H by (cbv [size]; try break_match; lia)
               end
             | _ => lia
             end.

    { Time solve_case. (* [] *) (* 0.015s *) }
    { Time solve_case. (* [ADD32] *) (* 5.915s *) }
    { Time solve_case. (* [ADD32, MOV64] *) (* 70.809s *) }
    { Time solve_case. (* [SHR64] *)(* 6.428s *) }
    { Time solve_case. (* [SHR64, MOV64] *) (* 75.004s *) }
    { Time solve_case. (* [SHL64] *) (* 6.03s *) }
    { Time solve_case. (* [SHL64, MOV64] *) (* 75.503s *) }
    { Time solve_case. (* [MOV64] *) (* 0.66s *) }
    { Time solve_case. (* [MOV64, ADD32] *) (* 155.61s *) }
    { Time solve_case. (* [MOV64, SHR64] *) (* 163.046s *) }
    { Time solve_case. (* [MOV64, SHL64] *) (* 163.357s *) }
    { Time solve_case. (* [MOV64, MOV64] *) (* 8.522s *) }
    { Time solve_case. (* [MOV64, MOV64, MOV64] *) (* 98.43s *) }
  Qed.
End Optimal.