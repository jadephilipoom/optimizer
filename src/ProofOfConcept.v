Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

(* Implementation of maps is left abstract for now *)
Class map_impl A :=
  {
    map : forall B : Type, Type;
    get : forall {B}, map B -> A -> B;
    update : forall {B}, map B -> A -> B -> map B;
    empty : forall {B} (default:B), map B;
    get_empty : forall B (d:B) a, get (empty d) a = d;
    get_update_eq : forall B a b (m : map B), get (update m a b) a = b;
    get_update_neq : forall B a1 a2 b (m : map B), a1 <> a2 -> get (update m a1 b) a2 = get m a2;
  }.
Arguments map _ {_} _.

(* Util : eventually will be in a separate file *)
Module Z.
  Lemma pow_base_lt a b : 1 < a -> 1 < b -> a < a ^ b.
  Proof.
    intros. apply Z.le_lt_trans with (m:=a^1); [ rewrite Z.pow_1_r; lia | ].
    apply Z.pow_lt_mono_r; lia.
  Qed.

  Definition seq start len :=
    List.map Z.of_nat (seq (Z.to_nat start) (Z.to_nat len)).
  Lemma in_seq start len x :
    0 <= start -> 0 <= len ->
    In x (seq start len) <-> (start <= x < start + len).
  Proof.
    intros; cbv [seq]. rewrite in_map_iff.
    split.
    { destruct 1 as [n [? Hin]]. subst x.
      apply in_seq in Hin.
      rewrite <-(Z2Nat.id start), <-(Z2Nat.id len); lia. }
    { intros. exists (Z.to_nat x).
      rewrite in_seq.
      split; [ rewrite Z2Nat.id; lia | ].
      rewrite <-Z2Nat.inj_add by lia.
      split; [ apply Z2Nat.inj_le | apply Z2Nat.inj_lt]; lia. }
  Qed.
End Z.

Lemma map_nil {A B} (f:A -> B): List.map f [] = []. Proof. reflexivity. Qed.
Lemma nth_default_nil {A} (d:A) i : nth_default d [] i = d. Proof. destruct i; reflexivity. Qed.
Lemma nth_default_cons_0 {A} (d:A) l0 l : nth_default d (l0 :: l) 0 = l0. Proof. reflexivity. Qed.
Lemma nth_default_cons_S {A} (d:A) l0 l i : nth_default d (l0 :: l) (S i) = nth_default d l i. Proof. reflexivity. Qed.
Lemma length_nil {A} : length (@nil A) = 0%nat. Proof. reflexivity. Qed.
Lemma length_cons {A} (a0 : A) l : length (a0 :: l) = S (length l). Proof. reflexivity. Qed.
Hint Rewrite @get_update_eq @get_empty @get_update_neq using congruence :  push_mapt.
Hint Rewrite @map_cons @map_nil : push_map.
Hint Rewrite @nth_default_nil @nth_default_cons_0 @nth_default_cons_S : push_nth_default.
Hint Rewrite @length_nil @length_cons : distr_length.
Definition minimum {A lt}
           (lt_dec : forall a1 a2 : A,
               {lt a1 a2} + {~ lt a1 a2})
           default ls : A :=
  fold_right
    (fun (current next : A) =>
       if lt_dec next current
       then next
       else current)
    default
    ls.
Lemma minimum_correct A lt lt_dec
      (lt_irr : forall a, ~ lt a a)
      (lt_asymm : forall a b, lt a b -> ~ lt b a)
      (nlt_trans : forall a b c, ~ lt b a -> ~ lt c b -> ~ lt c a)
      default ls :
  forall a,
    In a ls ->
    ~ lt a (@minimum A lt lt_dec default ls).
Proof.
  cbv [minimum]; induction ls; cbn [In fold_right]; [tauto|].
  destruct 1; subst;
    repeat match goal with
             |- context [if ?x then _ else _] => destruct x
           end; eauto.
Qed.
Lemma in_minimum A lt lt_dec default ls :
  @minimum A lt lt_dec default ls = default
  \/ In (minimum lt_dec default ls) ls.
Proof.
  cbv [minimum]; induction ls; cbn [In fold_right]; [tauto|].
  repeat match goal with
           |- context [if ?x then _ else _] => destruct x
         end; tauto.
Qed.
Ltac solve_zrange :=
  solve [repeat match goal with
                | |- _ /\ _ => split
                | _ => lia
                | _ => apply Z.div_le_lower_bound
                | _ => apply Z.div_lt_upper_bound
                | _ => apply Z.div_le_upper_bound
                end].
Ltac zero_bounds :=
  repeat match goal with
           | _ => lia
           | |- _ >= 0 => apply Z.ge_le
           | |- _ > 0 => apply Z.gt_lt
           | |- 0 < _ ^ _ => apply Z.pow_pos_nonneg
           | |- 0 <= _ ^ _ => apply Z.pow_nonneg
           | |- 0 <= Z.of_nat _ => apply Nat2Z.is_nonneg
           | |- 1 < _ ^ _ => apply Z.pow_gt_1
         end.
Ltac distr_length :=
  autorewrite with distr_length in *; try lia.
(* TODO: improve *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  | H : context [match ?x with _ => _ end] |- _ => destruct x
  end.
Ltac inversion_Forall :=
  repeat match goal with
         | H : Forall _ (?x :: _) |- _ =>
           let a := fresh "a" in
           let l := fresh "l" in
           inversion H as [ | a l ] ; clear H; subst a; subst l
         | H : Forall _ [] |- _ => clear H
         end.
Ltac destruction :=
  repeat match goal with
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : ?x = ?x |- _ => destruct H
         end.
Local Ltac cleanup :=
  repeat match goal with
         | _ => progress inversion_Forall
         | _ => progress autorewrite with distr_length in *
         end.

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


(* Machine model *)
Module Machine.
  Section Machine.
    Context {register flag instruction : Set}.
    Context {reg_mapt : map_impl register} {flag_mapt : map_impl flag}. (* we use abstract maps to keep track of state *)
    Context {register_size : register -> Z}
            {flag_spec : Z (* destination register size *) -> flag -> Z -> bool}.
    Context {flags_written : instruction -> list flag}
            {spec : instruction -> list Z -> (flag -> bool) -> Z}
            {precondition : instruction -> register -> list (register + Z) -> Prop}.
    Local Notation arg := (register + Z)%type.

    Inductive program : Type :=
    | Ret : register -> program
    | Instr :
        instruction ->
        register (* destination *) ->
        list arg (* arguments *) ->
        program (* continuation *) ->
        program
    .

    Inductive valid : program -> Prop :=
    | valid_ret : forall r, valid (Ret r)
    | valid_instr : forall i rd args cont,
        precondition i rd args ->
        valid cont ->
        valid (Instr i rd args cont)
    .

    Definition arg_value (ctx : map register Z) (x:arg) : Z :=
      match x with
      | inl r => get ctx r
      | inr z => z
      end.

    Fixpoint exec (e : program) (ctx : map register Z) (flag_ctx : map flag bool) : Z :=
      match e with
      | Ret r => get ctx r
      | Instr i rd args cont =>
        let result := i.(spec) (List.map (arg_value ctx) args) (get flag_ctx) in
        let n := register_size rd in
        let ctx' := update ctx rd (result mod 2^n) in
        let flag_ctx' :=
            fold_right (fun f fctx => update fctx f (flag_spec n f result)) flag_ctx i.(flags_written) in
        exec cont ctx' flag_ctx'
      end.

    Definition valid_context (ctx : map register Z) := forall r, 0 <= get ctx r < 2^ (register_size r).

    Definition equivalent (p1 p2 : program) :=
      forall ctx fctx,
        valid_context ctx ->
        exec p1 ctx fctx = exec p2 ctx fctx.
  End Machine.

  (* TODO: these don't work for parsing and I've no idea why *)
  Notation "i % rd x ; p" := (Instr i rd (x :: nil) p) (at level 100, p at level 200, format "i  % rd  x ; '//' p").
  Notation "i % rd x y ; p" := (Instr i rd (x :: y :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y ; '//' p").
  Notation "i % rd x y z ; p" := (Instr i rd (x :: y :: z :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y  z ; '//' p").
End Machine.

Module Flags.
  Inductive flag : Set := C | Z.
  Definition flag_spec dst_size (f:flag) : BinInt.Z -> bool :=
    match f with
    | C => fun z => Z.testbit z dst_size
    | Z => Z.eqb 0
    end.
  Definition flag_eq_dec (f1 f2 : flag) : {f1 = f2} + {f1 <> f2}.
  Proof. destruct f1, f2; try tauto; right; congruence. Defined.
  Definition all_flags := [C ; Z].
End Flags.

Module Instructions.
  Section Instructions.
    Context {register : Set} {register_size : register -> Z}.

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
  End Instructions.
End Instructions.

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

Module CostModel.
  Import Machine.
  Section CostModel.
    Context {register flag instruction : Set}
            {reg_mapt : map_impl register}
            {flag_mapt : map_impl flag}
            {register_size : register -> Z}
            {instr_cost : instruction -> nat}
            {precondition : instruction -> register -> list (register + Z) -> Prop}.
    Local Notation program := (Machine.program (register:=register) (instruction:=instruction)).
    Local Notation valid := (Machine.valid (precondition:=precondition)).
    Context (equivalent : program -> program -> Prop).

    Fixpoint cost (p : program) : nat :=
      match p with
      | Ret r => 0
      | Instr i rd args cont => i.(instr_cost) + cost cont
      end.

    Definition optimal (p : program) : Prop :=
      forall p' : program,
        valid p'
        -> (equivalent p p')
        -> (cost p <= cost p')%nat.
  End CostModel.
End CostModel.

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

Module MachineProofs.
  Import Machine.
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
    end; cleanup.
End MachineProofs.

Module InstructionProofs.
  Import Machine. Import Instructions.
  Section InstructionProofs.
    Context {register : Set} {register_size : register -> Z}.
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
  End InstructionProofs.
  Hint Resolve precondition_dec instr_eq_dec : deciders.
End InstructionProofs.

Module RegisterProofs.
  Import Registers.
  Lemma all_registers_complete : forall r, In r all_registers.
  Proof. destruct r; cbn; tauto. Qed.
End RegisterProofs.

Module FlagProofs.
  Import Flags.
  Lemma all_flags_complete : forall f, In f all_flags.
  Proof. destruct f; cbn; tauto. Qed.
End FlagProofs.

Module Enumerators.
  Import Machine. Import MachineProofs.
  Section Enumerators.
    Context {instruction flag register : Set}
            {register_size : register -> Z}
            (instr_size : instruction -> Z)
            (instr_cost : instruction -> nat)
            (num_source_regs : instruction -> nat)
            (precondition : instruction -> register -> list (register + Z) -> Prop)
            (cost : program (instruction:=instruction)
                            (register:=register) -> nat)
            (all_flags : list flag)
            (all_registers : list register)
            (all_instructions : list instruction).
    (* strips away irrelevant details like swapping equivalent
    registers around. Eventually this will need to be a little more
    sophisticated as the cost model matures.  *)
    Definition abstract_program := list instruction.
    Fixpoint to_abstract (p : program (register:=register))
      : abstract_program :=
      match p with
      | Ret _ => []
      | Instr i _ _ cont => i :: to_abstract cont
      end.

    Fixpoint enumerate_under_cost' (fuel max_cost : nat)
      : list abstract_program :=
      match fuel with
      | O => [ ]
      | S fuel' =>
        [] ::
           flat_map (fun i =>
                       if lt_dec i.(instr_cost) max_cost
                       then
                         List.map (cons i)
                                  (enumerate_under_cost' fuel' (max_cost - i.(instr_cost)))
                       else []) all_instructions
      end.
    Definition enumerate_under_cost max_cost :=
      enumerate_under_cost' max_cost max_cost.

    (* Note : don't compute this! For proofs only. *)
    Fixpoint enumerate_possible_maps {A B} {mapt : map_impl A}
             (default : B) (possible_values : A -> list B)
             (keys : list A)
      : list (map A B) :=
      match keys with
      | [] => [empty default]
      | k :: keys' =>
        flat_map
          (fun m =>
             List.map (fun v => update m k v) (possible_values k))
          (enumerate_possible_maps default possible_values keys')
      end.

    Section with_reg_map.
      Context {reg_map : map_impl register}.
      Definition enumerate_contexts :=
        enumerate_possible_maps
          0
          (fun r => Z.seq 0 (2^(register_size r)))
          all_registers.
    End with_reg_map.

    Section with_flag_map.
      Context {flag_map : map_impl flag}.
      Definition enumerate_flag_contexts :=
        enumerate_possible_maps
          false
          (fun _ => [true; false])
          all_flags.
    End with_flag_map.

    Definition enumerate_argument_values (max_const : Z)
      : list (register + Z) :=
      List.map inr (Z.seq 0 max_const) ++ List.map inl all_registers.
    Fixpoint enumerate_arguments (max_val : Z) (n : nat) :=
      match n with
      | O => [ [] ]
      | S n' =>
        List.flat_map
          (fun x =>
             List.map (cons x) (enumerate_arguments max_val n'))
          (enumerate_argument_values max_val)
      end.
    Fixpoint enumerate_concrete (ap : abstract_program)
      : list program :=
      match ap with
      | [] => List.map Ret all_registers
      | i :: ap' =>
        List.flat_map
          (fun cont =>
             List.flat_map
               (fun args =>
                  List.map
                    (fun rd => Instr i rd args cont) all_registers)
               (enumerate_arguments
                  (2 ^ instr_size i)
                  i.(num_source_regs)))
          (enumerate_concrete ap')
      end.
    Definition enumerate_programs_under_cost max_cost :=
      List.flat_map enumerate_concrete
                    (enumerate_under_cost max_cost).

    Definition enumerate_under_cost_with_condition
               (condition : program -> bool) max_cost  : list program :=
      (List.filter condition (enumerate_programs_under_cost max_cost)).

    Section EnumeratorProofs.
      Context (instr_cost_pos : forall i, (0 < instr_cost i)%nat)
              (cost_Ret : forall r, cost (Ret r) = 0%nat)
              (cost_Instr :
                 forall i rd args cont,
                   (cost (Instr i rd args cont) = cost cont + instr_cost i)%nat)
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
                   {precondition i rd args} + {~ precondition i rd args})
              (register_size_pos : forall r, 0 < register_size r)
              (all_flags_complete : forall r, In r all_flags)
              (all_registers_complete : forall r, In r all_registers)
              (all_instructions_complete : forall i, In i all_instructions).
      Local Notation valid := (valid (precondition:=precondition)).

      Lemma enumerate_under_cost'_complete :
        forall p max_cost fuel,
          (max_cost <= fuel)%nat ->
          (cost p < max_cost)%nat ->
          In (to_abstract p) (enumerate_under_cost' fuel max_cost).
      Proof.
        induction p; intros; (destruct fuel; [lia|]); [ cbn; tauto | ].
        cbn [to_abstract enumerate_under_cost' flat_map].
        apply in_cons, in_flat_map.
        exists i. pose proof (instr_cost_pos i).
        split; [ apply all_instructions_complete | ].
        rewrite cost_Instr in *.
        break_match; [ | lia ].
        apply in_map, IHp; lia.
      Qed.
      Lemma enumerate_under_cost_complete p max_cost :
        (cost p < max_cost)%nat ->
        In (to_abstract p) (enumerate_under_cost max_cost).
      Proof. intros; apply enumerate_under_cost'_complete; lia. Qed.

      Lemma enumerate_under_cost'_bound :
        forall p max_cost fuel,
          (0 < max_cost <= fuel)%nat ->
          In (to_abstract p) (enumerate_under_cost' fuel max_cost) ->
          (cost p < max_cost)%nat.
      Proof.
        induction p; intros; (destruct fuel; [lia|]); [ rewrite cost_Ret; lia | ].
        cbn [to_abstract enumerate_under_cost' flat_map] in *.
        repeat match goal with
               | H : In _ (_ :: _) |- _ => inversion H; clear H; try discriminate
               | H : In _ [] |- _ => inversion H
               | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
               | H : In _ (flat_map _ _) |- _ => rewrite in_flat_map in H;
                                                   destruct H as [? [? ?] ]
               | H : In _ (List.map _ _) |- _ => rewrite in_map_iff in H;
                                                   destruct H as [? [? ?] ]
               | _ => rewrite cost_Instr
               | _ => progress break_match
               end.
        specialize (instr_cost_pos i).
        specialize (IHp (max_cost - instr_cost i)%nat fuel ltac:(lia) ltac:(auto)).
        lia.
      Qed.
      Lemma enumerate_under_cost_bound p max_cost :
        (0 < max_cost)%nat ->
        In (to_abstract p) (enumerate_under_cost max_cost) ->
        (cost p < max_cost)%nat.
      Proof.
        cbv [enumerate_under_cost]; intros.
        apply enumerate_under_cost'_bound with (fuel:=max_cost); auto; lia.
      Qed.

      Lemma enumerate_possible_maps_complete'
            A B mapt default possible_values keys
            (key_dec : forall k1 k2 : A, {k1 = k2} + {k1 <> k2}):
        forall m,
          (forall k, In (get m k) (possible_values k)) ->
          exists m',
            (forall k, In k keys -> get m k = get m' k) /\
            In m' (@enumerate_possible_maps A B mapt default possible_values keys).
      Proof.
        intros; induction keys as [|k ?];
          cbn [enumerate_possible_maps].
        { intros. exists (empty default). split.
          { intros.
            match goal with H : _ |- _ =>
                            apply in_nil in H; contradiction H
            end. }
          { apply in_eq. } }
        { intros. destruct IHkeys as [m' [? ?]].
          exists (update m' k (get m k)). split.
          { intro k2; destruct (key_dec k k2); [|destruct 1];
              subst; autorewrite with push_mapt; auto; congruence. }
          { apply in_flat_map. exists m'. auto using in_map. } }
      Qed.

      Lemma enumerate_possible_maps_complete
            A B (mapt : map_impl A) default possible_values keys
            (map_equiv :
               forall m1 m2 : map A B,
                 (forall a, get m1 a = get m2 a) ->
                 m1 = m2)
            (key_dec : forall k1 k2 : A, {k1 = k2} + {k1 <> k2}) :
        forall m,
          (forall k, In k keys) ->
          (forall k, In (get m k) (possible_values k)) ->
          In m (@enumerate_possible_maps A B mapt default possible_values keys).
      Proof.
        intros.
        destruct (enumerate_possible_maps_complete' A B mapt default possible_values keys key_dec _ ltac:(eassumption)) as [m' [Hget HIn]].
        replace m with m' by auto using eq_sym. auto.
      Qed.

      Section with_reg_map.
        Context {reg_map : map_impl register}
                (reg_eq_dec : forall r1 r2 : register,
                    {r1 = r2} + {r1 <> r2})
                (reg_map_equiv :
                   forall B (m1 m2 : map register B),
                     (forall a, get m1 a = get m2 a) ->
                     m1 = m2).
        Lemma enumerate_contexts_complete ctx :
          valid_context (register_size:=register_size) ctx ->
          In ctx enumerate_contexts.
        Proof.
          intros; apply enumerate_possible_maps_complete; auto; [ ].
          intro r.
          pose proof (valid_context_range register_size ctx r ltac:(auto)) as Hrange.
          apply Z.in_seq; lia.
        Qed.
      End with_reg_map.

      Section with_flag_map.
        Context {flag_map : map_impl flag}
                (flag_eq_dec : forall k1 k2 : flag, {k1 = k2} + {k1 <> k2})
                (flag_map_equiv :
                   forall B (m1 m2 : map flag B),
                     (forall a, get m1 a = get m2 a) ->
                     m1 = m2).
        Lemma enumerate_flag_contexts_complete fctx :
          In fctx enumerate_flag_contexts.
        Proof.
          intros; apply enumerate_possible_maps_complete; auto; [ ].
          intro f; destruct (get fctx f); cbn; tauto.
        Qed.
      End with_flag_map.

      Lemma enumerate_argument_values_complete i rd args :
        precondition i rd args ->
        Forall (fun a => In a (enumerate_argument_values (2 ^ instr_size i))) args.
      Proof.
        cbv [enumerate_argument_values]; intros.
        apply Forall_forall; intros.
        apply in_or_app.
        match goal with
        | a : register + Z |- _ => destruct a; [right|left]
        end.
        { apply in_map; auto. }
        { pose proof (precondition_instr_size _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
          apply in_map, Z.in_seq; lia. }
      Qed.

      Lemma enumerate_arguments_complete' i rd args :
        precondition i rd args ->
        In args
           (enumerate_arguments (2 ^ (instr_size i)) (length args)).
      Proof.
        intro Hpre; apply enumerate_argument_values_complete in Hpre.
        induction args as [|a args]; intros; cleanup.
        { cbn; tauto. }
        { cbn [enumerate_arguments].
          apply in_flat_map. exists a.
          auto using in_map. }
      Qed.

      Lemma enumerate_arguments_complete i rd args :
        precondition i rd args ->
        In args
           (enumerate_arguments (2 ^ i.(instr_size))
                                (i.(num_source_regs))).
      Proof.
        intros.
        erewrite <-precondition_num_source_regs by eauto.
        eauto using enumerate_arguments_complete'.
      Qed.

      Lemma enumerate_concrete_complete p:
        valid p ->
        In p (enumerate_concrete (to_abstract p)).
      Proof.
        induction p; intros; cbn [to_abstract enumerate_concrete];
          repeat match goal with
                 | _ => inversion_valid
                 | _ => apply in_flat_map;
                          eexists; split; [ solve [eauto using enumerate_arguments_complete] | ]
                 | _ => apply in_map_iff;
                          eexists; split; [ solve [eauto] | ]
                 | _ => solve [auto] 
                 end.
      Qed.
      Lemma enumerate_concrete_to_abstract p :
        forall x,
          In p (enumerate_concrete x) ->
          x = to_abstract p.
      Proof.
        induction p; destruct x; cbn [to_abstract enumerate_concrete];
          repeat match goal with
                 | _ => progress intros
                 | H : In _ (_ :: _) |- _ => inversion H; clear H; try discriminate
                 | H : In _ [] |- _ => inversion H
                 | H : ?f _ _ = ?f _ _ |- _ => progress (inversion H; clear H; subst)
                 | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress (inversion H; clear H; subst)
                 | H : In _ (flat_map _ _) |- _ => rewrite in_flat_map in H;
                                                     destruct H as [? [? ?] ]
                 | H : In _ (List.map _ _) |- _ => rewrite in_map_iff in H;
                                                     destruct H as [? [? ?] ]
                 | _ => congruence
                 end.
        rewrite (IHp x); auto.
      Qed.

      Lemma enumerate_programs_under_cost_complete p c :
        valid p ->
        (cost p < c)%nat ->
        In p (enumerate_programs_under_cost c).
      Proof.
        intros; cbv [enumerate_programs_under_cost].
        apply in_flat_map. exists (to_abstract p).
        auto using enumerate_under_cost_complete, enumerate_concrete_complete.
      Qed.

      Lemma enumerate_programs_under_cost_bound p c :
        (0 < c)%nat ->
        In p (enumerate_programs_under_cost c) ->
        (cost p < c)%nat.
      Proof.
        cbv [enumerate_programs_under_cost].
        rewrite in_flat_map. destruct 2 as [? [? ?]].
        repeat match goal with
               | H : _ |- _ => apply enumerate_concrete_to_abstract in H; subst
               | H : _ |- _ => apply enumerate_under_cost_bound in H; lia
               end.
      Qed.

      Lemma enumerate_programs_under_cost_complete_alt p c :
        ~ In p (enumerate_programs_under_cost c) ->
        (~ valid p) \/ (~ (cost p < c))%nat.
      Proof.
        intros; pose proof (enumerate_programs_under_cost_complete p c).
        apply Decidable.not_and.
        { destruct (valid_dec precondition_dec p); [left | right]; tauto. }
        { destruct 1; intros; tauto. }
      Qed.

      Lemma enumerate_under_cost_with_condition_complete cond max_cost p :
        cond p = true -> valid p -> (cost p < max_cost)%nat ->
        In p (enumerate_under_cost_with_condition cond max_cost).
      Proof.
        cbv [enumerate_under_cost_with_condition]; intros.
        apply filter_In.
        split; repeat break_match; try tauto;
          auto using enumerate_programs_under_cost_complete.
      Qed.
      Lemma enumerate_under_cost_with_condition_sound cond max_cost p :
        In p (enumerate_under_cost_with_condition cond max_cost) ->
        cond p = true.
      Proof.
        cbv [enumerate_under_cost_with_condition].
        rewrite filter_In.
        repeat break_match; intros;
          repeat match goal with H : _ /\ _ |- _ => destruct H end;
          auto; congruence.
      Qed.
      Lemma enumerate_under_cost_with_condition_bound cond max_cost p :
        (0 < max_cost)%nat ->
        In p (enumerate_under_cost_with_condition cond max_cost) ->
        (cost p < max_cost)%nat.
      Proof.
        cbv [enumerate_under_cost_with_condition].
        rewrite filter_In.
        repeat break_match; intros;
          repeat match goal with H : _ /\ _ |- _ => destruct H end.
        auto using enumerate_programs_under_cost_bound.
      Qed.
    End EnumeratorProofs.
  End Enumerators.
End Enumerators.


Module Optimality.
  Import Machine. Import MachineProofs.
  (* Show that it's possible to select the optimal program by brute force *)
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
    Print CostModel.optimal.
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
        destruct (in_minimum _ _ dec d ls)
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
        destruct (in_minimum _ _ dec d ls)
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
        destruct (in_minimum _ _ dec d ls)
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
End Optimality.

Module Glue.
  Import Maps.
  Notation exec := (Machine.exec
                      (register_size:=Registers.size)
                      (flag_spec:=Flags.flag_spec)
                      (flags_written:=Instructions.flags_written)
                      (spec:=Instructions.spec)).
  Notation precondition :=
    (Instructions.precondition (register_size:=Registers.size)).
  Notation valid := (Machine.valid
                       (register:=Registers.register)
                       (precondition:=precondition)).
  Notation program := (Machine.program
                         (register:=Registers.register)
                         (instruction:=Instructions.instruction)).
  Notation valid_context := (Machine.valid_context
                               (register:=Registers.register)
                               (register_size:=Registers.size)).
  Notation equivalent := (Machine.equivalent
                            (register_size:=Registers.size)
                            (flag_spec := Flags.flag_spec)
                            (flags_written := Instructions.flags_written)
                            (spec := Instructions.spec)).
  Infix "==" := equivalent (at level 40).
  Notation cost := (CostModel.cost
                      (register:=Registers.register)
                      (instr_cost:=Instructions.instr_cost)).
  Notation optimal := (CostModel.optimal
                         (instr_cost:=Instructions.instr_cost)
                         (precondition:=precondition)
                         equivalent).

  (* TODO: make this rely on fewer things (for instance, parameterize over [equivalent]) *)
  Notation optimal_limited_domain_equiv :=
    (Optimality.optimal_limited_domain_equiv
       reg_map_equiv
       flag_map_equiv
       Instructions.instr_size
       Registers.size
       Instructions.instr_cost
       Instructions.num_source_regs
       precondition
       Flags.flag_spec
       Instructions.flags_written
       Instructions.spec
       Flags.flag_eq_dec
       Registers.reg_eq_dec
       Instructions.instr_eq_dec
       (fun m1 m2 => reg_map_dec m1 m2 Z.eq_dec)
       (fun m1 m2 => flag_map_dec m1 m2 Bool.bool_dec)
       Flags.all_flags
       Registers.all_registers
       Instructions.all_instructions
       FlagProofs.all_flags_complete
       RegisterProofs.all_registers_complete
       InstructionProofs.all_instructions_complete
       InstructionProofs.instr_cost_pos
       InstructionProofs.precondition_instr_size
       InstructionProofs.precondition_length_args
       InstructionProofs.precondition_dec
    ).
End Glue.

Module CandidateGenerators.
  Module All.
    Import Machine. Import Enumerators. Import Glue.

    Definition rep (ap : abstract_program) (p : program) : Prop := to_abstract p = ap.
    Definition rep_enum :=
      (enumerate_concrete Instructions.instr_size Instructions.num_source_regs Registers.all_registers).
    Lemma rep_enum_complete t p : valid p -> rep t p -> In p (rep_enum t).
    Proof.
      cbv [rep rep_enum]. intros; subst.
      eapply enumerate_concrete_complete;
        eauto using RegisterProofs.all_registers_complete,
        InstructionProofs.precondition_length_args,
        InstructionProofs.precondition_instr_size.
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
        auto using InstructionProofs.instr_cost_pos, InstructionProofs.all_instructions_complete.
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
End CandidateGenerators.

Module Examples.
  Import Instructions. Import Machine. Import Registers. Import CostModel.
  Import Maps. Import Glue.
  Import InstructionProofs.

  Definition examples : list program :=
    [
      (Ret r0); (* simplest program *)

        (* move value in r3 to r2 and return it *)
        (Instr MOV64 r2 (%r3 :: nil) (Ret r2));
        
        (* r0 + r1 with 32-bit add, result in r0 *)
        (Instr ADD32 r0 (%r0 :: %r1 :: nil) (Ret r0));

        (* r0 + r1 with 32-bit add, result in r2 (which is oversized) *)
        (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Ret r2));

        (* r0 + r1 with 64-bit add, result in r2 *)
        (Instr ADD64 r2 (%r0 :: %r1 :: nil) (Ret r2));

        (* (r0 + r1) >> 1 with 32-bit add, result in r2 *)
        (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2)));

        (* (r0 + r1) >> 1 with 64-bit add, result in r2 *)
        (Instr ADD64 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2)))
    ].

  Lemma examples_valid : Forall valid examples.
  Proof.
    repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
      try break_match; try lia.
  Qed.

  Hint Unfold
       Machine.equivalent Machine.exec 
       CostModel.optimal CostModel.cost
       Instructions.instr_cost Instructions.precondition.
  Ltac simplify := autounfold; cbn [size value spec arg_value].

  (* prove sum using 32- and 64- bit adds give the same result *)
  Section SumEquiv.
    Definition sum :=
      Eval compute in (nth_default (Ret r0) examples 5). (* ADD32 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
    Definition sum' :=
      Eval compute in (nth_default (Ret r0) examples 6). (* ADD64 r2 r0 r1; SHR64 r2 r2 $1; Ret r2 *)
    Hint Unfold sum sum'.
    
    Lemma sums_equiv : sum == sum'.
    Proof.
      repeat match goal with
             | _ => progress (intros; autounfold; simplify)
             | _ => progress autorewrite with push_map push_mapt push_nth_default
             | _ => progress MachineProofs.pose_valid_context_range
             | |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia
             end.
      reflexivity.
    Qed.
  End SumEquiv.

  (* Prove that programs are optimal *)
  Section Optimal.
    Definition simple_sum :=  (Instr ADD32 r0 (%r0 :: %r1 :: nil) (Ret r0)).
    (* Eval cbv [simple_sum] in simple_sum. (* ADD32 r2 r0 r1; Ret r2 *) *)
    Hint Unfold simple_sum.

    Lemma simple_sum_valid : valid simple_sum.
    Proof.
      repeat econstructor; cbn [arg_size size instr_size Pos.size Z.to_pos];
        try break_match; try lia.
    Qed.
    Lemma simple_sum_optimal : optimal simple_sum.
    Proof.
      apply (CandidateGenerators.All.optimal_limited_domain_equiv simple_sum simple_sum_valid).
      cbn. repeat econstructor.
      { intro P; inversion 1.
        destruct P; cbn [Enumerators.to_abstract] in *; try congruence; [ ].
        cbv [simple_sum equivalent].
        intro.
        (* TODO: use some test vectors to prove these two are not equivalent. *)
    Admitted.

    Definition sum_shift :=
      (Instr ADD32 r2 (%r0 :: %r1 :: nil) (Instr SHR64 r2 (%r2 :: $1 :: nil) (Ret r2))).
    (* Eval cbv [sum_shift] in sum_shift. (* ADD32 %r2 %r0 %r1; SHR64 %r2 %r2 $1; Ret r2 *) *)
    Hint Unfold sum_shift.

    Lemma sum_shift_optimal : optimal sum_shift.
    Proof.
    Admitted.
  End Optimal.
End Examples.
    
    