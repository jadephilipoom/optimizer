Require Import Coq.ZArith.ZArith.
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
           | |- 0 <= Z.of_nat _ => apply Nat2Z.is_nonneg
           | |- 1 < _ ^ _ => apply Z.pow_gt_1
         end.
Ltac distr_length :=
  autorewrite with distr_length in *; try lia.
(* TODO: improve *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  end.


(* Machine model *)
Module Machine.
  Section Machine.
    Context {register flag instruction : Set}.
    Context {reg_mapt : map_impl register} {flag_mapt : map_impl flag}. (* we use abstract maps to keep track of state *)
    Context {register_size : register -> nat}
            {flag_spec : nat (* destination register size *) -> flag -> Z -> bool}.
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
        let ctx' := update ctx rd (result mod 2^(Z.of_nat n)) in
        let flag_ctx' :=
            fold_right (fun f fctx => update fctx f (flag_spec n f result)) flag_ctx i.(flags_written) in
        exec cont ctx' flag_ctx'
      end.

    Definition valid_context (ctx : map register Z) := forall r, 0 <= get ctx r < 2^ (Z.of_nat (register_size r)).

  End Machine.

  Module Notations.
    Notation "i % rd x ; p" := (Instr i rd (x :: nil) p) (at level 100, p at level 200, format "i  % rd  x ; '//' p").
    Notation "i % rd x y ; p" := (Instr i rd (x :: y :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y ; '//' p").
    Notation "i % rd x y z ; p" := (Instr i rd (x :: y :: z :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y  z ; '//' p").
  End Notations.
End Machine.

Module Flags.
  Inductive flag : Set := C | Z.
  Definition flag_spec (dst_size:nat) (f:flag) : BinInt.Z -> bool :=
    match f with
    | C => fun z => Z.testbit z (Z.of_nat dst_size)
    | Z => Z.eqb 0
    end.
End Flags.

Module Instructions.
  Section Instructions.
    Context {register : Set} {register_size : register -> nat}.

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

    Definition instr_size (i:instruction) : nat :=
      match i with
      | ADD32 => 32
      | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 | MOV64 => 64
      end.

    Definition num_source_regs (i:instruction) : nat :=
      match i with
      | ADD32 | ADD64 | ADC64 | SUB64 | MUL64 | SHR64 | SHL64 => 2
      | MOV64 => 1
      end.

    Definition arg_size (x : register + Z) : nat :=
      match x with
      | inl r => register_size r
      | inr z =>
        if Z_lt_dec z 0
        then 0
        else Pos.to_nat (Pos.size (Z.to_pos z))
      end.

    Definition precondition (i:instruction) (rd:register) (args:list (register + Z)) : Prop :=
      length args = num_source_regs i
      /\ Forall (fun r => (0 < arg_size r <= instr_size i)%nat) args
      /\ (register_size rd >= instr_size i)%nat.
  End Instructions.
End Instructions.

Module Registers.
  Inductive register : Set := r0 | r1 | r2 | r3 | r4 | r5 | r6.
  Definition size (r:register) : nat :=
    match r with
    | r0 | r1 => 32%nat
    | r2 | r3 | r4 | r5 | r6 => 64%nat
    end.
  Notation "$ y" := (@inr register Z y) (at level 40, format "$ y").
  Notation "% r" := (@inl register Z r) (at level 40, format "% r").
End Registers.

Module CostModel.
  Import Instructions.
  Section CostModel.
    Context {register : Set} {size : register -> nat}.
    Local Notation program := (Machine.program (register:=register) (instruction:=instruction)).

    Definition instr_cost (i:instruction) : nat :=
      match i with
      | ADD32 => 2
      | ADD64 | ADC64 | SUB64 => 4
      | MUL64 => 8
      | SHR64 | SHL64 => 2
      | MOV64 => 1
      end.
    Fixpoint cost (p : program) : nat :=
      match p with
      | Machine.Ret r => 0
      | Machine.Instr i rd args cont => i.(instr_cost) + cost cont
      end.

    Definition optimal (equiv : program -> program -> Prop) (p : program) : Prop :=
      forall p' : program,
        Machine.valid (precondition:=precondition (register_size:=size)) p'
        -> (equiv p p')
        -> (cost p <= cost p')%nat.
  End CostModel.
End CostModel.


Module Maps.
  Module Generic.
    Section Generic.
      Context {A : Type} {A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2} }.

      Inductive t {B} : Type :=
      | Empty : B -> t
      | Update : t -> A -> B -> t
      .

      Fixpoint get {B} (m : @t B) (k : A) : B :=
        match m with
        | Empty d => d
        | Update m' a b => if A_eq_dec k a then b else get m' k
        end.

      Instance impl : map_impl A.
      Proof.
        apply Build_map_impl with (map:=@t) (get:=@get) (update:=@Update) (empty:=@Empty).
        { reflexivity. }
        { intros; cbn. break_match; congruence. }
        { intros; cbn. break_match; congruence. }
      Defined.
    End Generic.
  End Generic.

  Lemma get_update_full
        {A B} {mapt : map_impl A}
        {A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}}
        (m: map A B) a1 a2 b:
    get (update m a1 b) a2 = if A_eq_dec a1 a2 then b else get m a2.
  Proof. break_match; subst; autorewrite with push_mapt; reflexivity. Qed.

  Definition reg_eq_dec (r1 r2 : Registers.register) : {r1 = r2} + {r1 <> r2}.
  Proof.
    destruct r1, r2; try (left; congruence); right; congruence.
  Defined.

  Definition flag_eq_dec (f1 f2 : Flags.flag) : {f1 = f2} + {f1 <> f2}.
  Proof.
    destruct f1, f2; try (left; congruence); right; congruence.
  Defined.

  Instance reg_mapt : map_impl Registers.register := @Generic.impl _ reg_eq_dec.
  Instance flag_mapt : map_impl Flags.flag := @Generic.impl _ flag_eq_dec.
End Maps.

Module Glue.
  Import Maps.
  Definition exec := Machine.exec
                       (register_size:=Registers.size)
                       (flag_spec:=Flags.flag_spec)
                       (flags_written:=Instructions.flags_written)
                       (spec:=Instructions.spec).
  Definition valid := Machine.valid
                        (register:=Registers.register)
                        (precondition:=Instructions.precondition
                                         (register_size:=Registers.size)).
  Definition program := Machine.program
                          (register:=Registers.register)
                          (instruction:=Instructions.instruction).
  Definition valid_context := Machine.valid_context
                                (register:=Registers.register)
                                (register_size:=Registers.size).
  Definition precondition := Instructions.precondition (register_size:=Registers.size).
  Definition equivalent (p1 p2 : program) :=
    forall ctx fctx,
      valid_context ctx ->
      exec p1 ctx fctx = exec p2 ctx fctx.
  Infix "==" := equivalent (at level 100).
  Definition optimal := CostModel.optimal (size:=Registers.size) equivalent.
End Glue.

Module InstructionProofs.
  Import Instructions.
  Section InstructionProofs.
    Context {register : Set} {register_size : register -> nat}.
    (* TODO: simplify/automate; probably want a push_pos2z tactic, etc *)
    Lemma arg_size_constant_upper_bound x u :
      (0 < arg_size (register_size:=register_size) (inr x) <= u)%nat ->
      0 <= x < 2 ^ Z.of_nat u.
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
        apply inj_le in Hupper.
        rewrite positive_nat_Z in Hupper.
        lia. }
    Qed.
  End InstructionProofs.
End InstructionProofs.

Module CostModelProofs.
  Import CostModel. Import Instructions.
  Section CostModelProofs.
    Context {register : Set} {register_size : register -> nat}.
    Definition min_instr_cost : nat := 1.
    Lemma min_instr_cost_correct : forall i, (min_instr_cost <= instr_cost i)%nat.
    Proof. intros; destruct i; cbv [min_instr_cost instr_cost]; lia. Qed.
    Fixpoint depth (p : Machine.program (register:=register)
                                        (instruction:=instruction)) : nat :=
      match p with
      | Machine.Ret _ => 0
      | Machine.Instr _ _ _ cont => S (depth cont)
      end.
    Lemma depth_min_cost :
      forall p, ((depth p) * min_instr_cost <= cost p)%nat.
    Proof.
      induction p; intros; [ reflexivity | ]. cbn [depth cost].
      pose proof min_instr_cost_correct i. lia.
    Qed.
    Lemma length_args i rd args cont :
      Machine.valid
        (precondition:=Instructions.precondition (register_size:=register_size))
        (Machine.Instr i rd args cont) ->
      length args = i.(num_source_regs).
    Proof. inversion 1; intros; subst. cbv [precondition] in *. tauto. Qed.
  End CostModelProofs.
End CostModelProofs.

Module Examples.
  Import Instructions. Import Machine. Import Registers. Import CostModel.
  Import Machine.Notations. Import Maps. Import Glue.
  Import InstructionProofs. Import CostModelProofs.

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
  Proof. repeat econstructor. Qed.

  Lemma valid_context_range ctx r :
    valid_context ctx -> 0 <= get ctx r < 2 ^ (Z.of_nat (Registers.size r)).
  Proof. auto. Qed.

  Ltac pose_valid_context_range :=
    match goal with
    | H : valid_context ?ctx |- context [get ?ctx ?r] =>
      progress (match goal with
                | _ : 0 <= get ctx r < _ |- _ => idtac
                | _ =>
                  let H':= fresh in pose proof (valid_context_range ctx r H) as H'; autounfold in H'
                end)
    end.

  Hint Unfold
       equivalent exec Machine.exec 
       optimal CostModel.optimal CostModel.cost CostModel.instr_cost
       precondition Instructions.precondition.
  Ltac simplify := autounfold; cbn [size value spec arg_value].

  (* prove sum using 32- and 64- bit adds give the same result *)
  Section SumEquiv.
    Definition sum :=
      Eval compute in (nth_default (Ret r0) examples 5). (* ADD32 r2 r0 r1; SHR64 r2 r2 #1; Ret r2 *)
    Definition sum' :=
      Eval compute in (nth_default (Ret r0) examples 6). (* ADD64 r2 r0 r1; SHR64 r2 r2 #1; Ret r2 *)
    Hint Unfold sum sum'.
    
    Lemma sums_equiv : sum == sum'.
    Proof.
      repeat match goal with
             | _ => progress (intros; autounfold; simplify)
             | _ => progress autorewrite with push_map push_mapt push_nth_default
             | _ => progress pose_valid_context_range
             | |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia
             end.
      reflexivity.
    Qed.
  End SumEquiv.

  (* Prove that programs are optimal *)
  Section Optimal.
    Definition simple_sum :=
      Eval compute in (nth_default (Ret r0) examples 3). (* ADD32 r2 r0 r1; Ret r2 *)
    Hint Unfold simple_sum.

    Local Ltac prove_valid_ctx :=
      econstructor; autorewrite with push_mapt;
      rewrite ?(get_update_full (A_eq_dec:=reg_eq_dec)); cbv [size];
      repeat break_match; subst; autorewrite with push_mapt; lia.
    Local Ltac destruct_args :=
      match goal with H : Machine.valid (Instr _ _ ?args _) |- _ =>
                      let H' := fresh in
                      pose proof (length_args _ _ _ _ H) as H';
                      cbv [num_source_regs] in H';
                      repeat (destruct args as [|? args]; distr_length)
      end; repeat match goal with H : ?x = ?x |- _ => clear H end.
    Local Ltac inversion_Forall :=
      repeat match goal with
             | H : Forall _ (?x :: _) |- _ =>
               let a := fresh "a" in
               let l := fresh "l" in
               inversion H as [ | a l ] ; clear H; subst a; subst l
             | H : Forall _ [] |- _ => clear H
             end.
    Local Ltac inversion_valid :=
      repeat
        (match goal with
             | H : Machine.valid (Instr ?i ?rd ?args ?cont) |- _ =>
               inversion H; clear H;
               try match goal with H' : ?x = i |- _ => subst x end;
               try match goal with H' : ?x = rd |- _ => subst x end;
               try match goal with H' : ?x = args |- _ => subst x end;
               try match goal with H' : ?x = cont |- _ => subst x end
         end;
         repeat match goal with
                | H : Instructions.precondition _ _ _ |- _ =>
                  let H' := fresh in
                  inversion H as [? H']; clear H;
                  repeat match type of H' with
                           _ /\ _ =>
                           let H'':= fresh in destruct H' as [H'' H']
                         end
                | _ => progress inversion_Forall
                | _ => progress autorewrite with distr_length in *
                | _ => progress cbn [instr_size num_source_regs] in *
                end).
    Local Ltac pose_not_equivalent :=
      match goal with H : ?p1 == ?p2 |- _ =>
                      let H' := fresh in
                      assert (exists ctx, exec p1 ctx (empty false) <>
                                          exec p2 ctx (empty false)
                                          /\ valid_context ctx) as H';
                      [| destruct H' as [? [H' ?] ]; solve [auto] ]
      end.
    Lemma simple_sum_optimal : optimal simple_sum.
    Proof.
      repeat intro.
      assert (forall r, 2 < 2 ^ Z.of_nat (size r)).
      { destruct r; cbn [size]; apply Z.pow_base_lt; lia. }
      repeat match goal with
             | p : Machine.program |- _ =>
               destruct p as [? | i]; [ | destruct i ];
                 try solve [simplify; lia]
             end;
        exfalso; try destruct_args; pose_not_equivalent.
      (* leaves us with all programs that are strictly lower-cost than
      simple_sum -- Ret and MOV/Ret *)
      (* based on the unknown registers/arguments in context,
            construct counterexample contexts. Eventually, this should
            be done more automatically. *)
      1: (exists (update (update (empty 0) r0 1) r1 1)).
      2: match goal with
         | a : register + Z |- _ =>
           exists (update (update (empty 0) r0 1) r1
                          (match a with
                           | inr z => if Z.eq_dec z 2 then 2 else 1
                           | _ => 1
                           end))
         end.
      all: split; [ | solve [prove_valid_ctx] ]; autounfold; simplify;
        autorewrite with push_map push_nth_default push_mapt.
      all:repeat match goal with
                 | _ => break_match; subst
                 | _ => progress simplify
                 | _ => progress autorewrite with push_mapt
                 | H : _ |- _ => apply arg_size_constant_upper_bound in H
                 | _ => rewrite (get_update_full (A_eq_dec := reg_eq_dec))
                 | H : context[forall r, _ < 2 ^ (Z.of_nat (size r))]
                   |- context [?x mod 2 ^ (Z.of_nat (size ?r))] =>
                   rewrite (Z.mod_small x (2 ^ (Z.of_nat (size r)))) by
                       (specialize (H r); lia)
                 | H : context [?x < ?a ^ ?b] |- context [?x mod ?a ^ ?c] =>
                   rewrite (Z.mod_small x (a ^ c))
                     by (pose proof (Z.pow_le_mono_r 2 b c); lia)
                 | _ => rewrite Z.mod_small by lia
                 | _ => lia
                 | _ => progress inversion_valid
                 end.
    Qed.
  End Optimal.
End Examples.
    
    