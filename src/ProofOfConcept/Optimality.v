Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.MachineProofs.
Require Import Optimizer.System.
Require Import Optimizer.ProofOfConcept.CostModel. (* TODO: factor out dependency on specific ProofOfConcept things so the proofs can be reused *)
Require Import Optimizer.ProofOfConcept.Enumerators.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Require Import Optimizer.Util.Tactics.
Import ListNotations.
Local Open Scope Z_scope.
Import Machine.Machine.

Section Optimality.
  Context `{instrt : instr_impl}.
  Existing Instance reg_mapt. Existing Instance flag_mapt.
  Existing Instance reg_enum. Existing Instance flag_enum. Existing Instance instr_enum.
  Hint Resolve reg_eq_dec flag_eq_dec instr_eq_dec : deciders.

  Context (cost : program -> nat)
          (instr_cost_pos : forall i rd args cont, (cost cont < cost (Instr i rd args cont))%nat).
  Context (enumerate_programs_under_cost : nat -> list program)
          (enumerate_under_cost_with_condition : (program -> bool) -> nat -> list program).
  Context (enumerate_programs_under_cost_complete :
             forall p c,
               ~ In p (enumerate_programs_under_cost c) ->
               ~ valid p \/ ~ (cost p < c)%nat)
          (enumerate_under_cost_with_condition_complete :
             forall cond c p,
               cond p = true ->
               valid p ->
               (cost p < c)%nat ->
               In p (enumerate_under_cost_with_condition cond c))
          (enumerate_under_cost_with_condition_sound :
             forall cond c p,
               In p (enumerate_under_cost_with_condition cond c) -> cond p = true)
          (enumerate_under_cost_with_condition_bound :
             forall cond c p,
               (0 < c)%nat -> In p (enumerate_under_cost_with_condition cond c) ->
               (cost p < c)%nat)
          (enumerate_under_cost_with_condition_zero :
             forall cond, enumerate_under_cost_with_condition cond 0 = []).
  Context (all_contexts : list (map register Z))
          (all_contexts_complete :
             forall ctx, valid_context ctx -> In ctx all_contexts).
  Context (reg_map_equiv :
             forall B (m1 m2 : map register B),
               (forall a, get m1 a = get m2 a) ->
               m1 = m2)
          (flag_map_equiv :
             forall B (m1 m2 : map flag B),
               (forall a, get m1 a = get m2 a) ->
               m1 = m2)
          (context_eq_dec : forall ctx1 ctx2 : map register Z, {ctx1 = ctx2} + {ctx1 <> ctx2})
          (flag_context_eq_dec : forall fctx1 fctx2 : map flag bool, {fctx1 = fctx2} + {fctx1 <> fctx2}).
  Local Notation equiv_dec :=
    (equiv_dec all_contexts all_contexts_complete (fctx_enum flag_map_equiv) context_eq_dec flag_context_eq_dec).
  Local Infix "==" := equivalent (at level 40).
  Existing Instance fctx_enum.
  Hint Resolve valid_dec : deciders.

  Definition optimal (p : program) : Prop :=
    forall p' : program,
      valid p'
      -> (equivalent p p')
      -> (cost p <= cost p')%nat.

  Local Ltac use_epuc_complete_alt :=
    match goal with
      H : ~ In _ _ |- _ =>
      apply enumerate_programs_under_cost_complete in H;
      auto; [ ]; (* solve side conditions *)
      destruct H; (tauto || lia) (* solve remaining goal *)
    end.

  (* TODO: these should probably move eventually *)
  Lemma equivalent_refl p : p == p.
  Proof. cbv [equivalent]; auto. Qed.
  Lemma equivalent_sym p1 p2 : (p1 == p2) -> p2 == p1.
  Proof. cbv [equivalent]; auto using eq_sym. Qed.
  Lemma equivalent_trans p1 p2 p3 :
    (p1 == p2) -> (p2 == p3) -> (p1 == p3).
  Proof. cbv [equivalent]; eauto using eq_trans. Qed.

  Lemma optimal_dec p : {optimal p} + {~ optimal p}.
  Proof.
    cbv [optimal].
    apply dec_forall with (enum:=enumerate_programs_under_cost (cost p)).
    { apply program_eq_dec; auto using reg_eq_dec, instr_eq_dec. }
    { intros; apply dec_imp;
        eauto using dec_imp, all_contexts_complete, enum_complete, equiv_dec with deciders. }
    { intros. use_epuc_complete_alt. }
  Qed.

  Definition optimal_condition p p' : bool :=
    if valid_dec p'
    then if equiv_dec p p'
         then true
         else false
    else false.
  Definition optimal_program_candidates p :=
    enumerate_under_cost_with_condition
      (optimal_condition p)
      (cost p).

  Definition brute_force_optimal p : program :=
    minimum (fun p1 p2 => lt_dec (cost p1) (cost p2))
            p
            (optimal_program_candidates p).

  Lemma optimal_program_candidates_complete p p' :
    valid p' -> (p == p') -> (cost p' < cost p)%nat ->
    In p' (optimal_program_candidates p).
  Proof.
    cbv [optimal_program_candidates optimal_condition]; intros.
    eapply enumerate_under_cost_with_condition_complete; eauto; [ ].
    repeat break_match; try tauto.
  Qed.
  Lemma optimal_program_candidates_sound p p' :
    In p' (optimal_program_candidates p) ->
    optimal_condition p p' = true.
  Proof.
    cbv [optimal_program_candidates].
    eapply enumerate_under_cost_with_condition_sound; eauto.
  Qed.
  Lemma optimal_program_candidates_equiv p p' :
    In p' (optimal_program_candidates p) ->
    p == p'.
  Proof.
    let H := fresh in
    intro H; apply optimal_program_candidates_sound in H;
      cbv [optimal_condition] in H.
    repeat break_match; try discriminate; auto.
  Qed.
  Lemma optimal_program_candidates_valid p p' :
    In p' (optimal_program_candidates p) ->
    valid p'.
  Proof.
    let H := fresh in
    intro H; apply optimal_program_candidates_sound in H;
      cbv [optimal_condition] in H.
    repeat break_match; try discriminate; auto.
  Qed.
  Lemma optimal_program_candidates_bound p p' :
    (0 < cost p)%nat ->
    In p' (optimal_program_candidates p) ->
    (cost p' < cost p)%nat.
  Proof.
    cbv [optimal_program_candidates];
      eauto using Enumerators.enumerate_under_cost_with_condition_bound.
  Qed.
  Lemma brute_force_optimal_min p p' :
    In p' (optimal_program_candidates p) ->
    (cost (brute_force_optimal p) <= cost p')%nat.
  Proof.
    intros; cbv [optimal brute_force_optimal].
    apply Nat.nlt_ge.
    apply minimum_correct with
        (lt_dec:=(fun p1 p2 => lt_dec (cost p1) (cost p2)));
      intros; auto; lia.
  Qed.

  Lemma optimal_program_candidates_Ret p :
    cost p = 0%nat ->
    optimal_program_candidates p = [].
  Proof.
    intros; cbv [optimal_program_candidates optimal_condition].
    destruct p as [|i r l p]; [|pose proof (instr_cost_pos i r l p); lia].
    match goal with H : _ = 0%nat |- _ => rewrite H end; auto.
  Qed.
  
  Lemma brute_force_optimal_bound p :
    (cost (brute_force_optimal p) <= cost p)%nat.
  Proof.
    intros; cbv [optimal brute_force_optimal].
    match goal with
      |- context [minimum ?dec ?d ?ls] =>
      destruct (in_minimum dec d ls)
    end.
    { rewrite H; eauto using Nat.le_refl. }
    {
      destruct (lt_dec 0 (cost p)).
      auto using Nat.lt_le_incl, optimal_program_candidates_bound.
      rewrite optimal_program_candidates_Ret by lia.
      cbn. lia. }
  Qed.
  Lemma brute_force_optimal_equiv p :
    (p == brute_force_optimal p).
  Proof.
    intros; cbv [brute_force_optimal].
    pose proof (equivalent_refl p).
    match goal with
      |- context [minimum ?dec ?d ?ls] =>
      destruct (in_minimum dec d ls)
    end.
    { congruence. }
    { auto using optimal_program_candidates_equiv. }
  Qed.
  Lemma brute_force_optimal_valid p :
    valid p ->
    valid (brute_force_optimal p).
  Proof.
    intros; cbv [brute_force_optimal].
    match goal with
      |- context [minimum ?dec ?d ?ls] =>
      destruct (in_minimum dec d ls)
    end.
    { congruence. }
    { eauto using optimal_program_candidates_valid. }
  Qed.
  Lemma brute_force_optimal_correct p :
    optimal (brute_force_optimal p).
  Proof.
    cbv [optimal]; intros.
    destruct (le_dec (cost p) (cost p'));
      [ pose proof (brute_force_optimal_bound p); lia | ].
    apply brute_force_optimal_min.
    apply optimal_program_candidates_complete; try lia;
      eauto using equivalent_trans, brute_force_optimal_equiv.
  Qed.
  Lemma optimal_exists p :
    valid p ->
    { op : program | valid op /\ (p == op) /\ optimal op }.
  Proof.
    exists (brute_force_optimal p).
    auto using brute_force_optimal_equiv, brute_force_optimal_valid, brute_force_optimal_correct.
  Qed.
  Lemma optimal_cost_neq p p' :
    valid p -> valid p' ->
    optimal p -> ~ optimal p' -> (p == p') ->
    (cost p < cost p')%nat.
  Proof.
    intros.
    match goal with
      H : ~ optimal ?p |- _ =>
      apply not_forall_exists with
        (enum:=enumerate_programs_under_cost (cost p)) in H; [ destruct H as [p2 ?] | .. ]
    end;
      intros; try apply dec_imp;
        eauto using dec_imp, all_contexts_complete, enum_complete, equiv_dec with deciders;
        try use_epuc_complete_alt; [ ].
    repeat match goal with
           | H : _ |- _ =>
             apply Decidable.not_imp in H;
               [ | solve [auto using dec_decidable, valid_dec, equiv_dec] ];
               destruct H
           | H : optimal _ |- _ =>
             specialize (H p2); repeat (specialize (H ltac:(eauto using equivalent_trans)))
           end.
    lia.
  Qed.
  Lemma optimal_exists_dec p :
    valid p ->
    { optimal p } + { exists p', optimal p'
                                 /\ valid p'
                                 /\ (p == p')
                                 /\ (cost p' < cost p)%nat }.
  Proof.
    intros.
    destruct (optimal_dec p); [tauto | right ].
    exists (brute_force_optimal p).
    pose proof (brute_force_optimal_correct p).
    pose proof (brute_force_optimal_equiv p).
    pose proof (brute_force_optimal_valid p).
    match goal with
    | H: ~ optimal ?p, H' : optimal ?op |- _ =>
      let H := fresh in
      pose proof (H' p) as H;
        repeat (specialize (H ltac:(auto using equivalent_sym)))
    end.
    repeat split; auto using optimal_cost_neq, equivalent_sym.
  Qed.

  Section Filtered.
    Context {T} (rep : T -> program -> Prop)
            (rep_enum : T -> list program)
            (rep_enum_complete :
               forall t p,
                 valid p ->
                 rep t p ->
                 In p (rep_enum t))
            (rep_enum_sound :
               forall t p,
                 In p (rep_enum t) ->
                 rep t p)
            (p_spec : program)
            (valid_p_spec : valid p_spec)
            (candidates : list T)
            (candidates_complete :
               (* if there is an optimal program that is strictly faster than p_spec,
                      then there is an optimal program in candidates *)
               forall op,
                 optimal op ->
                 equivalent p_spec op ->
                 (cost op < cost p_spec)%nat ->
                 exists t,
                   rep t op /\
                   In t candidates).

    Lemma optimal_limited_domain_equiv' :
      (Forall (fun t => ~ Exists (fun p' => valid p' /\ equivalent p_spec p') (rep_enum t)) candidates) ->
      optimal p_spec.
    Proof.
      destruct (optimal_exists_dec p_spec); [ assumption | tauto | ].
      destruction.
      pose proof (candidates_complete _ ltac:(eauto) ltac:(eauto) ltac:(eauto)).
      destruction.
      rewrite Forall_Exists_neg, Exists_exists.
      let H := fresh in intro H; exfalso; apply H.
      eexists; split; eauto; [ ].
      apply Exists_exists.
      eexists; split; eauto.
    Qed.

    Lemma optimal_limited_domain_equiv :
      (Forall (fun t => forall p', rep t p' -> valid p' -> ~ equivalent p_spec p') candidates) ->
      optimal p_spec.
    Proof.
      intros; apply optimal_limited_domain_equiv'; auto; [ ].
      eapply Forall_impl; [ | eassumption].
      intros; apply Forall_Exists_neg, Forall_forall.
      cbv beta in *.
      match goal with H : forall p : program, ?rep _ p -> valid p -> ~ _ == p |- forall _ : program, _ =>
                      intro x; intros; specialize (H x ltac:(eauto))
      end. tauto.
    Qed.
  End Filtered.
End Optimality.
