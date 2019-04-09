Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma map_nil {A B} (f:A -> B): map f [] = []. Proof. reflexivity. Qed.
Lemma nth_default_nil {A} (d:A) i : nth_default d [] i = d. Proof. destruct i; reflexivity. Qed.
Lemma nth_default_cons_0 {A} (d:A) l0 l : nth_default d (l0 :: l) 0 = l0. Proof. reflexivity. Qed.
Lemma nth_default_cons_S {A} (d:A) l0 l i : nth_default d (l0 :: l) (S i) = nth_default d l i. Proof. reflexivity. Qed.
Lemma length_nil {A} : length (@nil A) = 0%nat. Proof. reflexivity. Qed.
Lemma length_cons {A} (a0 : A) l : length (a0 :: l) = S (length l). Proof. reflexivity. Qed.
Hint Rewrite @map_cons @map_nil : push_map.
Hint Rewrite @nth_default_nil @nth_default_cons_0 @nth_default_cons_S : push_nth_default.
Hint Rewrite @length_nil @length_cons : distr_length.


Section Minimum.
  Context {A lt} (lt_dec : forall a1 a2 : A, {lt a1 a2} + {~ lt a1 a2}) (default : A).
  Context (lt_irr : forall a, ~ lt a a)
          (lt_asymm : forall a b, lt a b -> ~ lt b a)
          (nlt_trans : forall a b c, ~ lt b a -> ~ lt c b -> ~ lt c a).

  Definition minimum ls : A :=
    fold_right
      (fun (current next : A) =>
         if lt_dec next current
         then next
         else current)
      default
      ls.
  Lemma minimum_correct ls a : In a ls -> ~ lt a (minimum ls).
  Proof.
    cbv [minimum]; induction ls; cbn [In fold_right]; [tauto|].
    destruct 1; subst;
      repeat match goal with
               |- context [if ?x then _ else _] => destruct x
             end; eauto.
  Qed.
  Lemma in_minimum ls : minimum ls = default \/ In (minimum ls) ls.
  Proof.
    cbv [minimum]; induction ls; cbn [In fold_right]; [tauto|].
    repeat match goal with
             |- context [if ?x then _ else _] => destruct x
           end; tauto.
  Qed.
End Minimum.

Ltac distr_length :=
  autorewrite with distr_length in *; try lia.
Ltac inversion_Forall :=
  repeat match goal with
         | H : Forall _ (?x :: _) |- _ =>
           let a := fresh "a" in
           let l := fresh "l" in
           inversion H as [ | a l ] ; clear H; subst a; subst l
         | H : Forall _ [] |- _ => clear H
         end.
Ltac list_cleanup :=
  repeat match goal with
         | _ => progress inversion_Forall
         | _ => progress autorewrite with distr_length in *
         end.
