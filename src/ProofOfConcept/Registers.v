Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Module Registers.
  Inductive register : Set := r0 | r1 | r2 | r3 | r4 | r5 | r6.
  Definition size (r:register) : Z :=
    match r with
    | r0 | r1 => 32
    | r2 | r3 | r4 | r5 | r6 => 64
    end.
  Definition reg_eq_dec (r1 r2 : register) : {r1 = r2} + {r1 <> r2}.
  Proof. destruct r1, r2; try tauto; right; congruence. Defined.
  Hint Resolve reg_eq_dec : deciders.
  Definition all_registers := [r0;r1;r2;r3;r4;r5;r6].
  Notation "$ y" := (@inr register Z y) (at level 40, format "$ y").
  Notation "% r" := (@inl register Z r) (at level 40, format "% r").
End Registers.

Section Proofs.
  Lemma all_registers_complete : forall r, In r Registers.all_registers.
  Proof. destruct r; cbn; tauto. Qed.
End Proofs.
