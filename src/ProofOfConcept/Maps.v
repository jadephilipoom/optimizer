Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.ProofOfConcept.Flags.
Require Import Optimizer.ProofOfConcept.Registers.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.Tactics.
Import ListNotations.

Module Maps.
  Module RegMaps.
    Import Registers.

    Record reg_map {B : Type} : Type :=
      {
        val_r0 : B;
        val_r1 : B;
        val_r2 : B;
        val_r3 : B;
        val_r4 : B;
        val_r5 : B;
        val_r6 : B;
      }.

    Definition get {B} (m : reg_map) (r : register) : B :=
      match r with
      | r0 => m.(val_r0)
      | r1 => m.(val_r1)
      | r2 => m.(val_r2)
      | r3 => m.(val_r3)
      | r4 => m.(val_r4)
      | r5 => m.(val_r5)
      | r6 => m.(val_r6)
      end.

    Definition update {B} (m : reg_map) (r : register) (v : B) : reg_map :=
      {|
        val_r0 := if (reg_eq_dec r r0) then v else m.(val_r0);
        val_r1 := if (reg_eq_dec r r1) then v else m.(val_r1);
        val_r2 := if (reg_eq_dec r r2) then v else m.(val_r2);
        val_r3 := if (reg_eq_dec r r3) then v else m.(val_r3);
        val_r4 := if (reg_eq_dec r r4) then v else m.(val_r4);
        val_r5 := if (reg_eq_dec r r5) then v else m.(val_r5);
        val_r6 := if (reg_eq_dec r r6) then v else m.(val_r6);
      |}.

    Definition empty {B : Type} (default : B) : reg_map :=
      {|
        val_r0 := default;
        val_r1 := default;
        val_r2 := default;
        val_r3 := default;
        val_r4 := default;
        val_r5 := default;
        val_r6 := default;
      |}.

    Instance reg_mapt : map_impl register.
    Proof.
      apply Build_map_impl with (get:=@get) (update:=@update) (empty:=@empty).
      { intros. destruct a; reflexivity. }
      { intros. destruct a; reflexivity. }
      { intros. destruct a2; cbn; break_match; congruence. }
    Defined.
  End RegMaps.

  Module FlagMaps.
    Import Flags.

    Record flag_map {B : Type} :=
      {
        val_C : B;
        val_Z : B;
      }.

    Definition get {B} (m : flag_map) (f : flag) : B :=
      match f with
      | C => m.(val_C)
      | Z => m.(val_Z)
      end.

    Definition update {B} (m : flag_map) (f : flag) (v : B) : flag_map :=
      {|
        val_C := if (flag_eq_dec f C) then v else m.(val_C);
        val_Z := if (flag_eq_dec f Z) then v else m.(val_Z);
      |}.

    Definition empty {B : Type} (default : B) : flag_map :=
      {|
        val_C := default;
        val_Z := default;
      |}.

    Instance flag_mapt : map_impl flag.
    Proof.
      apply Build_map_impl with (get:=@get) (update:=@update) (empty:=@empty).
      { intros. destruct a; reflexivity. }
      { intros. destruct a; reflexivity. }
      { intros. destruct a2; cbn; break_match; congruence. }
    Defined.
  End FlagMaps.

  Lemma get_update_full
        {A B} {mapt : map_impl A}
        {A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}}
        (m: map A B) a1 a2 b:
    get (update m a1 b) a2 = if A_eq_dec a1 a2 then b else get m a2.
  Proof. break_match; subst; autorewrite with push_mapt; reflexivity. Qed.

  Lemma reg_get_update_full {B} (m : map Registers.register B) a1 a2 b:
    get (update m a1 b) a2 = if Registers.reg_eq_dec a1 a2 then b else get m a2.
  Proof. apply get_update_full. Qed.

  Lemma flag_get_update_full {B} (m : map Flags.flag B) a1 a2 b:
    get (update m a1 b) a2 = if Flags.flag_eq_dec a1 a2 then b else get m a2.
  Proof. apply get_update_full. Qed.

  Lemma reg_map_equiv B (m1 m2 : map Registers.register B) :
    (forall a, get m1 a = get m2 a) ->
    m1 = m2.
  Proof.
    intro Hequiv.
    set (regs:=Registers.all_registers).
    cbv [Registers.all_registers] in *.
    repeat match goal with
           | regs := ?r :: ?regs' |- _ =>
                     clear regs;
                       set (regs:=regs');
                       pose proof (Hequiv r)
           end; clear Hequiv.
    destruct m1, m2.
    cbn in *; subst; reflexivity.
  Qed.

  Lemma flag_map_equiv B (m1 m2 : map Flags.flag B) :
    (forall a, get m1 a = get m2 a) ->
    m1 = m2.
  Proof.
    intro Hequiv. set (flags:=Flags.all_flags).
    cbv [Flags.all_flags] in *.
    repeat match goal with
           | flags := ?f :: ?flags' |- _ =>
                      clear flags;
                        set (flags:=flags');
                        pose proof (Hequiv f)
           end; clear Hequiv.
    destruct m1, m2.
    cbn in *; subst; reflexivity.
  Qed.

  Definition reg_map_dec {A} (m1 m2 : map Registers.register A) :
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    {m1 = m2} + {m1 <> m2}.
  Proof. intros; destruct m1, m2. f_equal_dec. Defined.
  Hint Resolve @reg_map_dec : deciders.
  Definition flag_map_dec {A} (m1 m2 : map Flags.flag A) :
    (forall a1 a2 : A, {a1 = a2} + {a1 <> a2}) ->
    {m1 = m2} + {m1 <> m2}.
  Proof. intros; destruct m1, m2. f_equal_dec. Defined.
  Hint Resolve @flag_map_dec : deciders.
End Maps.
