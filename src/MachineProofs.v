Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Import ListNotations.
Local Open Scope Z_scope.
Import Machine.Machine.

Section MachineProofs.
  Context {instruction flag register : Set}
          {precondition : instruction -> register -> list (register+ Z) -> Prop}
          {reg_mapt : map_impl register}
          {flag_mapt : map_impl flag}
          (instruction_eq_dec : forall i1 i2 : instruction, {i1 = i2} + {i1 <> i2})
          (reg_eq_dec : forall r1 r2 : register, {r1 = r2} + {r1 <> r2})
          (register_size : register -> Z)
          (flag_spec : Z -> flag -> Z -> bool)
          (flags_written : instruction -> list flag)
          (spec : instruction -> list Z -> (flag -> bool) -> Z) 
          (all_registers : list register)
          (all_registers_complete : forall r, In r all_registers)
          (precondition_dec :
             forall i rd args,
               {precondition i rd args} + {~ precondition i rd args}).
  Local Notation valid_context := (valid_context (register_size:=register_size)).
  Local Notation valid := (valid (precondition:=precondition)).
  Local Notation equivalent := (equivalent (register_size:=register_size) (flag_spec:=flag_spec) (flags_written:=flags_written) (spec:=spec)).
  Hint Resolve instruction_eq_dec reg_eq_dec : deciders.

  Lemma valid_context_range ctx r :
    valid_context ctx ->
    0 <= get ctx r < 2 ^ (register_size r).
  Proof. auto. Qed.

  Definition valid_dec p : {valid p} + {~ valid p}.
  Proof.
    clear - precondition_dec; induction p;
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
    clear - reg_eq_dec all_registers_complete register_size; cbv [valid_context].
    apply dec_forall with (enum:=all_registers); [ solve [auto] | | ].
    { intro r.
      destruct (Z_le_dec 0 (get ctx r)); [| right; lia].
      destruct (Z_lt_dec (get ctx r) (2^(register_size r)));
        [left | right]; lia. }
    { intro r; specialize (all_registers_complete r); tauto. }
  Defined.
  Hint Resolve valid_context_dec : deciders.

  Definition arg_eq_dec (a1 a2 : register + Z) : {a1 = a2} + {a1 <> a2}.
  Proof. destruct a1, a2; try (right; congruence); f_equal_dec. Defined.
  Hint Resolve arg_eq_dec : deciders.

  Definition program_eq_dec :
    forall p1 p2 : program (register:=register)
                           (instruction:=instruction),
      {p1 = p2} + {p1 <> p2}.
  Proof. induction p1; destruct p2; try (right; congruence); f_equal_dec. Defined.

  Section with_context_enumerators.
    Context (all_contexts : list (map register Z))
            (all_flag_contexts : list (map flag bool))
            (all_contexts_complete : forall ctx, valid_context ctx -> In ctx all_contexts)
            (all_flag_contexts_complete : forall fctx, In fctx all_flag_contexts).
    Context (context_eq_dec : forall ctx1 ctx2 : map register Z, {ctx1 = ctx2} + {ctx1 <> ctx2})
            (flag_context_eq_dec : forall fctx1 fctx2 : map flag bool, {fctx1 = fctx2} + {fctx1 <> fctx2}).
    Hint Resolve context_eq_dec flag_context_eq_dec : deciders.

    Definition equiv_dec p1 p2 : {equivalent p1 p2} + {~ (equivalent p1 p2)}.
    Proof.
      repeat match goal with
             | _ => progress (intros; cbv [equivalent])
             | H : context [@In ?A _ ?ls] |- {forall (_ : ?A), _} + {~ (forall (_ : ?A), _)} =>
               apply dec_forall with (enum:=ls)
             | H : ~ In ?x ?ls |- _ => assert (In x ls) by auto; tauto
             | _ => solve [auto using dec_imp with deciders]
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
