Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.Machine.
Require Import Optimizer.ProofOfConcept.Enumerators.
Require Import Optimizer.ProofOfConcept.Instructions.
Require Import Optimizer.ProofOfConcept.Registers.
Require Import Optimizer.ProofOfConcept.Glue.
Import Machine.
Local Open Scope Z_scope.

Module All.
  Definition rep (ap : abstract_program) (p : program) : Prop := to_abstract p = ap.
  Definition rep_enum := (enumerate_concrete instr_size).
  Lemma rep_enum_complete t p : valid p -> rep t p -> In p (rep_enum t).
  Proof.
    cbv [rep rep_enum]. intros; subst.
    eapply enumerate_concrete_complete; eauto;
      apply precondition_length_args || apply precondition_instr_size.
  Qed.
  Lemma rep_enum_sound t p : In p (rep_enum t) -> rep t p.
  Proof.
    cbv [rep rep_enum]. intros.
    erewrite enumerate_concrete_to_abstract by eassumption.
    reflexivity.
  Qed.

  Definition candidates p := enumerate_under_cost instr_cost (cost p).
  Lemma candidates_complete p_spec op :
    optimal op ->
    equivalent p_spec op ->
    (cost op < cost p_spec)%nat ->
    exists t,
      rep t op /\ In t (candidates p_spec).
  Proof.
    intros. exists (to_abstract op).
    split; [reflexivity|]. cbv [candidates].
    eapply enumerate_under_cost_complete;
      eauto using instr_cost_pos, all_instructions_complete.
    intros; cbn; lia.
  Qed.

  Lemma optimal_limited_domain_equiv p_spec :
    valid p_spec ->
    Forall (fun ap => forall p' : program, rep ap p' -> valid p' -> ~ p_spec == p') (candidates p_spec) ->
    optimal p_spec.
  Proof.
    intros. pose proof (optimal_limited_domain_equiv rep).
    eauto using rep_enum_complete, rep_enum_sound, candidates_complete.
  Qed.
End All.
