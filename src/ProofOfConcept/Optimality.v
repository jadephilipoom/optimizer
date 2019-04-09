Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.MachineProofs.
Require Import Optimizer.ProofOfConcept.CostModel. (* TODO: factor out dependency on specific ProofOfConcept things so the proofs can be reused *)
Require Import Optimizer.ProofOfConcept.Enumerators.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Require Import Optimizer.Util.Tactics.
Import ListNotations.
Local Open Scope Z_scope.
Import Machine.Machine.

(* N.B. nothing in this section is intended to be run! These
  functions would take ages and exists just for proofs. *)
Section BruteForce.
  (* TODO : the contexts are getting out of hand. Need to decide who
    depends on whom, and move some stuff from context to actual
    implementations. Either that, or get a nice record-based
    precondition system set up. *)
  Context {instruction flag register : Set}
          {reg_mapt : map_impl register}
          {flag_mapt : map_impl flag}
          (reg_map_equiv :
             forall B (m1 m2 : map register B),
               (forall a, get m1 a = get m2 a) ->
               m1 = m2)
          (flag_map_equiv :
             forall B (m1 m2 : map flag B),
               (forall a, get m1 a = get m2 a) ->
               m1 = m2)
          (instr_size : instruction -> Z)
          (register_size : register -> Z)
          (instr_cost num_source_regs : instruction -> nat)
          (precondition : instruction -> register -> list (register + Z) -> Prop)
          (flag_spec : Z -> flag -> Z -> bool)
          (flags_written : instruction -> list flag)
          (spec : instruction -> list Z -> (flag -> bool) -> Z)
          (flag_eq_dec : forall f1 f2 : flag, {f1 = f2} + {f1 <> f2})
          (reg_eq_dec : forall r1 r2 : register, {r1 = r2} + {r1 <> r2})
          (instr_eq_dec : forall i1 i2 : instruction, {i1 = i2} + {i1 <> i2})
          (context_eq_dec : forall ctx1 ctx2 : map register Z, {ctx1 = ctx2} + {ctx1 <> ctx2})
          (flag_context_eq_dec : forall fctx1 fctx2 : map flag bool, {fctx1 = fctx2} + {fctx1 <> fctx2})
          (all_flags : list flag) (all_registers : list register) (all_instructions : list instruction).
  Context (all_flags_complete : forall f, In f all_flags)
          (all_registers_complete : forall r, In r all_registers)
          (all_instructions_complete : forall i, In i all_instructions)
          (instr_cost_pos : forall i, (0 < instr_cost i)%nat)
          (precondition_instr_size :
             forall i rd args x,
               precondition i rd args ->
               In (inr x) args ->
               0 <= x < 2^instr_size i)
          (precondition_num_source_regs :
             forall i rd args,
               precondition i rd args ->
               length args = num_source_regs i)
          (precondition_dec :
             forall i rd args,
               {precondition i rd args} + {~ precondition i rd args}).
  Hint Resolve valid_dec equiv_dec precondition_dec : deciders.
  Local Notation program := (@Machine.program register instruction).
  Local Notation valid := (valid (precondition:=precondition)).
  Local Notation valid_dec := (valid_dec precondition_dec).
  Local Notation enumerate_programs_under_cost :=
    (Enumerators.enumerate_programs_under_cost instr_size instr_cost num_source_regs all_registers all_instructions).
  Local Notation enumerate_under_cost_with_condition :=
    (Enumerators.enumerate_under_cost_with_condition instr_size instr_cost num_source_regs all_registers all_instructions).
  Local Notation all_contexts :=
    (Enumerators.enumerate_contexts (register_size:=register_size) all_registers).
  Local Notation all_flag_contexts := (Enumerators.enumerate_flag_contexts all_flags).
  Local Notation all_contexts_complete :=
    (Enumerators.enumerate_contexts_complete all_registers all_registers_complete reg_eq_dec reg_map_equiv).
  Local Notation all_flag_contexts_complete :=
    (Enumerators.enumerate_flag_contexts_complete all_flags all_flags_complete flag_eq_dec flag_map_equiv).
  Local Notation equiv_dec :=
    (equiv_dec reg_eq_dec register_size flag_spec flags_written spec all_registers all_registers_complete all_contexts all_flag_contexts all_contexts_complete all_flag_contexts_complete context_eq_dec flag_context_eq_dec).
  Local Notation cost := (CostModel.cost (register:=register) (instr_cost:=instr_cost)).
  Local Notation equivalent := (@equivalent _ _ _ _ _ register_size flag_spec flags_written spec).
  Local Notation optimal := (CostModel.optimal (instr_cost:=instr_cost) (precondition:=precondition) equivalent).
  Local Infix "==" := equivalent (at level 40).

  Local Ltac use_epuc_complete_alt :=
    match goal with
      H : ~ In _ _ |- _ =>
      apply Enumerators.enumerate_programs_under_cost_complete_alt with
      (precondition0:=precondition) (cost:=cost) in H;
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

  Lemma instr_cost_cost i rd args cont :
    (cost (Instr i rd args cont) = cost cont + instr_cost i)%nat.
  Proof. cbn [cost]; lia. Qed.
  Local Hint Resolve instr_cost_cost.

  Lemma optimal_dec p : {optimal p} + {~ optimal p}.
  Proof.
    cbv [optimal].
    apply dec_forall with (enum:=enumerate_programs_under_cost (cost p)).
    { apply program_eq_dec; auto using reg_eq_dec, instr_eq_dec. }
    { intros; apply dec_imp;
        eauto using dec_imp, all_contexts_complete, all_flag_contexts_complete with deciders. }
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
    eapply Enumerators.enumerate_under_cost_with_condition_complete; eauto; [ ].
    repeat break_match; try tauto.
  Qed.
  Lemma optimal_program_candidates_sound p p' :
    In p' (optimal_program_candidates p) ->
    optimal_condition p p' = true.
  Proof.
    cbv [optimal_program_candidates].
    eapply Enumerators.enumerate_under_cost_with_condition_sound; eauto.
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
    destruct p as [|i ?]; cbn [cost]; [|pose proof (instr_cost_pos i); lia].
    reflexivity.
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
        eauto using dec_imp, all_contexts_complete, all_flag_contexts_complete with deciders;
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
      (Forall (fun t => ~ Exists (equivalent p_spec) (rep_enum t)) candidates) ->
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
      (Forall (fun t => forall p', rep t p' -> ~ equivalent p_spec p') candidates) ->
      optimal p_spec.
    Proof.
      intros; apply optimal_limited_domain_equiv'; auto; [ ].
      eapply Forall_impl; [ | eassumption].
      intros; apply Forall_Exists_neg, Forall_forall; eauto.
    Qed.
  End Filtered.
End BruteForce.
