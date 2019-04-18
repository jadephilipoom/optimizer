Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Decidable.
Require Import Coq.Lists.List.
Require Import Optimizer.Util.Tactics.

Section Sumbool.
  Lemma dec_and A B : {A} + {~ A} -> {B} + {~ B} ->
                      {A /\ B} + {~ (A /\ B)}.
  Proof. tauto. Qed.
  Lemma dec_imp (A B : Prop) :
    {A} + {~ A} ->
    {B} + {~ B} ->
    {(A -> B)} + {~ (A -> B)}.
  Proof. tauto. Qed.

  Definition func_eq_dec A B (f:A -> B) (x y : A) :
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    (forall a1 a2, a1 <> a2 -> f a1 <> f a2) ->
    {f x = f y} + {f x <> f y}.
  Proof.
    intro A_eq_dec; destruct (A_eq_dec x y); [left|right];
      auto; congruence.
  Defined.

  Lemma dec_decidable A : {A} + {~ A} -> Decidable.decidable A.
  Proof. destruct 1; [left|right]; tauto. Qed.
  
  Section Finite.
    Context A (eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2})
            (P : A -> Prop) (P_dec : forall a, {P a} + {~ P a}).

    (* enum has all possible elements that would fail (e.g. all
    elements that satisfy a precondition in P) *)
    Section with_enum.
      Context enum (Henum : forall a, ~ In a enum -> P a).
      Lemma dec_forall_exists : {forall a, P a} + {exists a, ~ P a}.
      Proof.
        intros.
        destruct (Forall_Exists_dec P P_dec enum); [ left | right ];
          rewrite ?Forall_forall, ?Exists_exists in *.
        { intro a. destruct (in_dec eq_dec a enum); auto. }
        { destruction. eauto. }
      Qed.
      Lemma dec_forall : {forall a, P a} + {~ (forall a, P a)}.
      Proof.
        edestruct dec_forall_exists; try eassumption; [tauto|].
        right; intro.
        match goal with
        | H : exists a, ~ P a, H': forall a, P a |- _ =>
        let x := fresh in
        destruct H as [x ?]; specialize (H' x); tauto
        end.
      Qed.
      Lemma not_forall_exists : (~ (forall a, P a)) -> exists a, ~ P a.
      Proof. edestruct dec_forall_exists; try eassumption; tauto. Qed.
    End with_enum.

    Lemma dec_forall_dependent B (projA : B -> A) enumB :
      (forall b, ~ In b enumB -> P (projA b)) ->
      (forall a, ~ Exists (fun b => projA b = a) enumB -> P a) ->
      {forall a, P a} + {~ (forall a, P a)}.
    Proof.
      intros.
      destruct (Forall_Exists_dec (fun b => P (projA b)) (fun b=> P_dec (projA b)) enumB); [ left | right ];
        repeat match goal with
               | _ => destruction; subst; solve [eauto]
               | H : forall x, ~ Exists ?P ?ls -> _ |- forall _, _ =>
                 let a := fresh in
                 intro a;
                   destruct (Exists_dec ((fun x => P) a) ls); [ solve [eauto] | | solve [eauto] ]
               | _ => progress rewrite ?Forall_forall, ?Exists_exists in *
               end.
    Qed.
  End Finite.
End Sumbool.
Hint Resolve dec_and dec_imp
     Nat.eq_dec ge_dec gt_dec lt_dec le_dec
     Z.eq_dec Z_ge_dec Z_gt_dec Z_lt_dec Z_le_dec
     Bool.bool_dec
     list_eq_dec in_dec Forall_dec
     dec_decidable
  : deciders.
Ltac f_equal_dec' A B :=
  match A with
  | ?f ?a =>
    match B with
    | f a => left; reflexivity
    | ?g a => f_equal_dec' f g
    | f ?b =>
      let H := fresh in
      assert ({a = b} + {a <> b}) as H by auto with deciders;
      destruct H; [subst a|right; congruence]
    | ?g ?b => f_equal_dec' f g
    end
  end.
Ltac f_equal_dec :=
  repeat match goal with
         | |- {?A = ?B} + {?A <> ?B} =>
           f_equal_dec' A B
         end;
  try (left; reflexivity).
