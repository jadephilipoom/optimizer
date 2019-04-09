Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.Machine.
Require Import Optimizer.ProofOfConcept.Enumerators.
Require Import Optimizer.ProofOfConcept.Glue.
Require Import Optimizer.ProofOfConcept.Instructions.
Require Import Optimizer.ProofOfConcept.Registers.

Module All.
  Definition rep (ap : abstract_program) (p : program) : Prop := to_abstract p = ap.
  Definition rep_enum :=
    (enumerate_concrete Instructions.instr_size Instructions.num_source_regs Registers.all_registers).
  Lemma rep_enum_complete t p : valid p -> rep t p -> In p (rep_enum t).
  Proof.
    cbv [rep rep_enum]. intros; subst.
    eapply enumerate_concrete_complete;
      eauto using all_registers_complete, precondition_length_args, precondition_instr_size.
  Qed.
  Lemma rep_enum_sound t p : In p (rep_enum t) -> rep t p.
  Proof.
    cbv [rep rep_enum]. intros.
    erewrite enumerate_concrete_to_abstract by eassumption.
    reflexivity.
  Qed.

  Definition candidates p :=
    enumerate_under_cost Instructions.instr_cost Instructions.all_instructions (cost p).
  Lemma candidates_complete p_spec op :
    optimal op ->
    equivalent p_spec op ->
    (cost op < cost p_spec)%nat ->
    exists t,
      rep t op /\ In t (candidates p_spec).
  Proof.
    intros. exists (to_abstract op).
    split; [reflexivity|].
    cbv [candidates].
    apply enumerate_under_cost_complete with (cost:=cost);
      auto using instr_cost_pos, all_instructions_complete.
    intros; cbn; lia.
  Qed.

  Notation optimal_limited_domain_equiv :=
    (fun p valid_p =>
       optimal_limited_domain_equiv rep
                                    rep_enum
                                    rep_enum_complete
                                    rep_enum_sound
                                    p
                                    valid_p
                                    (candidates p)
                                    (candidates_complete p)).
End All.
