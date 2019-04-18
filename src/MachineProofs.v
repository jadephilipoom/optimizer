Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.System.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Import ListNotations.
Local Open Scope Z_scope.
Import Machine.Machine.

Section MachineProofs.
  Context `{instrt : instr_impl}.
  Existing Instance reg_mapt. Existing Instance flag_mapt.
  Existing Instance reg_enum. Existing Instance flag_enum.
  Hint Resolve instr_eq_dec reg_eq_dec : deciders.

  Lemma valid_context_range ctx r :
    valid_context ctx ->
    0 <= get ctx r < 2 ^ (register_size r).
  Proof. auto. Qed.

  Definition valid_dec p : {valid p} + {~ valid p}.
  Proof.
    induction p;
      repeat match goal with
             | |- context [valid (Instr ?i ?rd ?args _)] =>
               progress
                 (match goal with
                  | H : context [precondition i rd args] |- _ =>
                    idtac
                  | _ => destruct (precondition_dec i rd args)
                  end)
             | _ => destruct IHp
             | _ => left; constructor; solve [auto]
             | _ => right; inversion 1; tauto
             end.
  Defined.

  Definition valid_context_dec (ctx : map register Z) :
    {valid_context ctx} + {~ (valid_context ctx)}.
  Proof.
    cbv [valid_context].
    apply dec_forall with (enum:=enum); [ solve [auto with deciders] | | ].
    { intro r.
      destruct (Z_le_dec 0 (get ctx r)); [| right; lia].
      destruct (Z_lt_dec (get ctx r) (2^(register_size r)));
        [left | right]; lia. }
    { intro r; specialize (enum_complete r); tauto. }
  Defined.
  Hint Resolve valid_context_dec : deciders.

  Definition arg_eq_dec (a1 a2 : register + Z) : {a1 = a2} + {a1 <> a2}.
  Proof. destruct a1, a2; try (right; congruence); f_equal_dec. Defined.
  Hint Resolve arg_eq_dec : deciders.

  Definition program_eq_dec :
    forall p1 p2 : program, {p1 = p2} + {p1 <> p2}.
  Proof. induction p1; destruct p2; try (right; congruence); f_equal_dec. Defined.

  Section with_context_enumerators.
    Context (valid_contexts : list (map register Z))
            (valid_contexts_complete : forall ctx, valid_context ctx -> In ctx valid_contexts)
            (fctx_enum : enumerator (map flag bool)).
    Context (context_eq_dec : forall ctx1 ctx2 : map register Z, {ctx1 = ctx2} + {ctx1 <> ctx2})
            (flag_context_eq_dec : forall fctx1 fctx2 : map flag bool, {fctx1 = fctx2} + {fctx1 <> fctx2}).
    Hint Resolve context_eq_dec flag_context_eq_dec : deciders.

    Definition equiv_dec p1 p2 : {equivalent p1 p2} + {~ (equivalent p1 p2)}.
    Proof.
      repeat match goal with
             | _ => progress (intros; cbv [equivalent])
             | |- {forall (_ : ?A), _} + {~ (forall (_ : ?A), _)} =>
               apply dec_forall with (enum:=enum)
             | |- {forall (_ : ?A), _} + {~ (forall (_ : ?A), _)} =>
               apply dec_forall with (enum:=valid_contexts)
             | H : ~ In ?x ?ls |- _ => assert (In x ls) by auto using enum_complete; tauto
             | _ => tauto
             | _ => solve [apply enum_complete]
             | |- { _ } + { _ } => solve [auto using dec_imp with deciders]
             end.
    Qed.
  End with_context_enumerators.
End MachineProofs.
Hint Resolve valid_dec valid_context_dec arg_eq_dec program_eq_dec equiv_dec : deciders.

Ltac pose_valid_context_range :=
  match goal with
  | H : valid_context ?ctx |- context [get ?ctx ?r] =>
    progress (match goal with
              | _ : 0 <= get ctx r < _ |- _ => idtac
              | _ =>
                let H':= fresh in pose proof (valid_context_range ctx r H) as H'; autounfold in H'
              end)
  end.
Ltac inversion_valid :=
  match goal with
  | H : Machine.valid (Instr ?i ?rd ?args ?cont) |- _ =>
    inversion H; clear H;
    try match goal with H' : ?x = i |- _ => subst x end;
    try match goal with H' : ?x = rd |- _ => subst x end;
    try match goal with H' : ?x = args |- _ => subst x end;
    try match goal with H' : ?x = cont |- _ => subst x end
  end; list_cleanup.