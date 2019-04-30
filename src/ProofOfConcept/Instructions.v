Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.ProofOfConcept.Flags.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.Tactics.
Import ListNotations.
Local Open Scope Z_scope.

Section Defns.
  Context {register : Type} {register_size : register -> Z}.

  Local Notation "x '[' n ']'" := (List.nth_default 0 x n) (at level 0).
  Local Notation "x >> y" := (Z.shiftr x y) (at level 100).
  Local Notation "x << y" := (Z.shiftl x y) (at level 100).
  Local Coercion Z.b2z : bool >-> Z.

  Inductive instruction : Set := ADD32 | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 | MOV64.

  Definition flags_written (i:instruction) : list Flags.flag :=
    match i with
    | ADD32 | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 => (Flags.C :: Flags.Z :: nil)
    | MOV64 => nil
    end.

  Definition flags_read (i:instruction) : list Flags.flag :=
    match i with
    | ADC64 => (Flags.C :: nil)
    | ADD32 | ADD64| SUB64 | MUL64 | SHR64 | SHL64 | MOV64 => nil 
    end.

  Definition spec (i:instruction) (args : list Z) (fctx : Flags.flag -> bool) : Z :=
    match i with
    | ADD32 => args[0] + args[1]
    | ADD64 => args[0] + args[1]
    | ADC64 => args[0] + args[1] + fctx Flags.C
    | SUB64 => args[0] - args[1]
    | MUL64 => args[0] * args[1]
    | SHR64 => args[0] >> args[1]
    | SHL64 => args[0] << args[1]
    | MOV64 => args[0]
    end.

  Definition instr_size (i:instruction) : Z :=
    match i with
    | ADD32 => 32
    | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 | MOV64 => 64
    end.

  Definition num_source_regs (i:instruction) : nat :=
    match i with
    | ADD32 | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 => 2
    | MOV64 => 1
    end.

  Definition arg_size (x : register + Z) : Z :=
    match x with
    | inl r => register_size r
    | inr z =>
      if Z_lt_dec z 0
      then 0
      else Z.pos (Pos.size (Z.to_pos z))
    end.

  Definition precondition (i:instruction) (rd:register) (args:list (register + Z)) : Prop :=
    length args = num_source_regs i
    /\ Forall (fun r => 0 < arg_size r <= instr_size i) args
    /\ instr_size i <= register_size rd.

  Definition instr_cost (i:instruction) : nat :=
    match i with
    | ADD32 => 2
    | ADD64 | ADC64 | SUB64 => 4
    | MUL64 => 8
    | SHR64 | SHL64 => 2
    | MOV64 => 1
    end.

  Definition instr_eq_dec (i1 i2 : instruction) : {i1 = i2} + {i1 <> i2}.
  Proof. destruct i1, i2; try (right; congruence); left; reflexivity. Defined.

  (* TODO: is there a more elegant way to do this? *)
  Definition all_instructions := [ADD32; ADD64; ADC64; SUB64; MUL64; SHR64; SHL64; MOV64].
End Defns.

Section Proofs.
  Context {register : Type} {register_size : register -> Z}.
  (* TODO: simplify/automate; probably want a push_pos2z tactic, etc *)
  Lemma arg_size_constant_upper_bound x u :
    0 < arg_size (register_size:=register_size) (inr x) <= u ->
    0 <= x < 2 ^ u.
  Proof.
    cbv [arg_size]; break_match; intro Hrange;
      destruct Hrange as [Hlower Hupper]; [lia | split; [ lia | ] ].
    destruct (Z.eq_dec x 0); (* Z->positive proofs want x > 0 *)
      [ subst; apply Z.pow_pos_nonneg; lia | ].
    eapply Z.le_lt_trans with (m:=Z.pos (Z.to_pos x));
      [rewrite Z2Pos.id by lia; reflexivity | ].
    eapply Z.lt_le_trans with (m:=Z.pos (2^(Pos.size (Z.to_pos x)))).
    { auto using Pos2Z.pos_lt_pos, Pos.size_gt. }
    { rewrite Pos2Z.inj_pow.
      apply Z.pow_le_mono_r; [ lia | ].
      lia. }
  Qed.
  Lemma all_instructions_complete : forall i, In i all_instructions.
  Proof. destruct i; cbn; tauto. Qed.
  Lemma instr_cost_pos i : (0 < instr_cost i)%nat.
  Proof. destruct i; cbn; lia. Qed.

  Lemma precondition_length_args i rd args :
    precondition (register_size:=register_size) i rd args ->
    length args = i.(num_source_regs).
  Proof. inversion 1; intros; tauto. Qed.

  Lemma precondition_instr_size i rd args x :
    precondition (register_size:=register_size) i rd args ->
    In (inr x) args ->
    0 <= x < 2^instr_size i.
  Proof.
    inversion 1; intros. destruction.
    match goal with
    | H : _ |- _ => rewrite Forall_forall in H;
                      specialize (H (inr x) ltac:(assumption))
    end.
    apply arg_size_constant_upper_bound. lia.
  Qed.

  Definition precondition_dec i rd args :
    {precondition (register_size:=register_size) i rd args}
    + {~ precondition (register_size:=register_size) i rd args}.
  Proof. cbv [precondition]; auto with deciders. Defined.


  Context {flag_mapt : map_impl Flags.flag}.
  
  Lemma flags_read_correct i f :
    ~ (In f i.(flags_written)) ->
    forall v args flag_values,
      spec i args (get (update flag_values f v)) =
      spec i args (get (flag_values)).
  Proof.
    destruct i; destruct f;
      repeat match goal with
             | _ => progress intros
             | _ => progress cbn [flags_written spec In] in *
             | _ => reflexivity
             | _ => rewrite get_update_neq by congruence
             | _ => tauto
             end.
  Qed.
End Proofs.
Hint Resolve precondition_dec instr_eq_dec : deciders.