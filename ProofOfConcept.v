Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

(* Implementation of maps is left abstract for now *)
Class map_impl :=
  {
    map : forall A B : Type, Type;
    get : forall {A B}, map A B -> A -> B;
    update : forall {A B}, map A B -> A -> B -> map A B;
    empty : forall A B (default:B), map A B;
    get_empty : forall A B d a, get (empty A B d) a = d;
    get_update_eq : forall A B a b (m : map A B), get (update m a b) a = b;
    get_update_neq : forall A B a1 a2 b (m : map A B), a1 <> a2 -> get (update m a1 b) a2 = get m a2;
  }.

(* Machine model *)
Module Machine.
  Section Machine.
    Context {mapt : map_impl}. (* we use abstract maps to keep track of state *)
    Context {register flag instruction : Set}.
    Context {register_size : register -> nat}
            {register_value : (map register Z) -> register -> Z}
            {flag_spec : nat (* destination register size *) -> flag -> Z -> bool}.
    Context {cost : instruction -> nat}
            {flags_written : instruction -> list flag}
            {spec : instruction -> list Z -> (flag -> bool) -> Z}
            {precondition : instruction -> register -> list register -> Prop}.

    Inductive program : Type :=
    | Ret : register -> program
    | Instr :
        instruction ->
        register (* destination *) ->
        list register (* arguments *) ->
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

    Fixpoint exec (e : program) (ctx : map register Z) (flag_ctx : map flag bool) : Z :=
      match e with
      | Ret r => get ctx r
      | Instr i rd args cont =>
        let result := i.(spec) (List.map (register_value ctx) args) (get flag_ctx) in
        let n := register_size rd in
        let ctx' := update ctx rd (result mod 2^(Z.of_nat n)) in
        let flag_ctx' :=
            fold_right (fun f fctx => update fctx f (flag_spec n f result)) flag_ctx i.(flags_written) in
        exec cont ctx' flag_ctx'
      end.

    Fixpoint get_cost (e : program) : nat :=
      match e with
      | Ret r => 0
      | Instr i rd args cont => i.(cost) + get_cost cont
      end.

    Definition valid_context (ctx : map register Z) := forall r, 0 <= get ctx r < 2^ (Z.of_nat (register_size r)).

  End Machine.

  Module Notations.
    Notation "i rd x ; p" := (Instr i rd (x :: nil) p) (at level 100, p at level 200, format "i  rd  x ; '//' p").
    Notation "i rd x y ; p" := (Instr i rd (x :: y :: nil) p) (at level 100, p at level 200, format "i  rd  x  y ; '//' p").
    Notation "i rd x y z ; p" := (Instr i rd (x :: y :: z :: nil) p) (at level 100, p at level 200, format "i  rd  x  y  z ; '//' p").
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
    Context {register : Set} {size : register -> nat}.

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

    Definition precondition (i:instruction) (rd:register) (args:list register) : Prop :=
      length args = num_source_regs i
      /\ Forall (fun r => (size r <= instr_size i)%nat) args
      /\ (size rd >= instr_size i)%nat.
 
    Definition cost (i:instruction) : nat :=
      match i with
      | ADD32 => 2
      | ADD64 | ADC64 | SUB64 => 4
      | MUL64 => 8
      | SHR64 | SHL64 => 2
      | MOV64 => 1
      end.
    
  End Instructions.
End Instructions.

Module Registers.
  Inductive register : Set := r0 | r1 | r2 | r3 | r4 | r5 | r6 | const : Z -> register.
  Definition size (r:register) : nat :=
    match r with
    | r0 | r1 => 32%nat
    | r2 | r3 | r4 | r5 | r6 => 64%nat
    | const x => Z.to_nat (Z.log2 x)
    end.
  Definition value {mapt : map_impl} (ctx : map register Z) (r:register) : Z :=
    match r with
    | const x => x
    | _ => get ctx r
    end.
  Notation "'#' y" := (const y) (at level 30, format "# y").
End Registers.

Module Glue.
  Section with_mapt.
    Context {mapt : map_impl}.
    Definition exec := Machine.exec
                         (register_size:=Registers.size)
                         (register_value:=Registers.value)
                         (flag_spec:=Flags.flag_spec)
                         (flags_written:=Instructions.flags_written)
                         (spec:=Instructions.spec).
    Definition valid := Machine.valid
                          (register:=Registers.register)
                          (precondition:=Instructions.precondition (size:=Registers.size)).
    Definition program := Machine.program (register:=Registers.register) (instruction:=Instructions.instruction).
    Definition valid_context := Machine.valid_context
                                  (register:=Registers.register)
                                  (register_size:=Registers.size).
  End with_mapt.

  (* equivalence is quantified over all implementations of map *)
  Definition equivalent (p1 p2 : program) :=
    forall (mapt : map_impl) ctx fctx,
      valid_context ctx ->
      exec p1 ctx fctx = exec p2 ctx fctx.
  Infix "==" := equivalent (at level 100).
End Glue.

Module Examples.
  Import Instructions. Import Machine. Import Registers.
  Import Machine.Notations. Import Glue.

  Definition examples : list program :=
    [
      (Ret r0); (* simplest program *)

        (* move value in r3 to r2 and return it *)
        (Instr MOV64 r2 (r3 :: nil) (Ret r2));
        
        (* r0 + r1 with 32-bit add, result in r0 *)
        (Instr ADD32 r0 (r0 :: r1 :: nil) (Ret r0));

        (* r0 + r1 with 32-bit add, result in r2 (which is oversized) *)
        (Instr ADD32 r2 (r0 :: r1 :: nil) (Ret r2));

        (* r0 + r1 with 64-bit add, result in r2 *)
        (Instr ADD64 r2 (r0 :: r1 :: nil) (Ret r2));

        (* (r0 + r1) >> 1 with 32-bit add, result in r2 *)
        (Instr ADD32 r2 (r0 :: r1 :: nil) (Instr SHR64 r2 (r2 :: #1 :: nil) (Ret r2)));

        (* (r0 + r1) >> 1 with 64-bit add, result in r2 *)
        (Instr ADD64 r2 (r0 :: r1 :: nil) (Instr SHR64 r2 (r2 :: #1 :: nil) (Ret r2)))
    ].

  Lemma examples_valid : Forall valid examples.
  Proof. repeat econstructor. Qed.

  Lemma map_nil {A B} (f:A -> B): List.map f [] = []. Proof. reflexivity. Qed.
  Lemma nth_default_nil {A} (d:A) i : nth_default d [] i = d. Proof. destruct i; reflexivity. Qed.
  Lemma nth_default_cons_0 {A} (d:A) l0 l : nth_default d (l0 :: l) 0 = l0. Proof. reflexivity. Qed.
  Lemma nth_default_cons_S {A} (d:A) l0 l i : nth_default d (l0 :: l) (S i) = nth_default d l i. Proof. reflexivity. Qed.
  Hint Rewrite @get_update_eq @get_empty : push_mapt.
  Hint Rewrite @map_cons @map_nil : push_map.
  Hint Rewrite @nth_default_nil @nth_default_cons_0 @nth_default_cons_S : push_nth_default.

  (* prove sum using 32- and 64- bit adds give the same result *)
  Definition sum := Eval compute in (nth_default (Ret r0) examples 5). (* ADD32 r2 r0 r1; SHR64 r2 r2 #1; Ret r2 *)
  Definition sum' := Eval compute in (nth_default (Ret r0) examples 6). (* ADD64 r2 r0 r1; SHR64 r2 r2 #1; Ret r2 *)

  Lemma valid_context_range {mapt: map_impl} ctx r :
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

  Ltac solve_zrange :=
    solve [repeat match goal with
                  | |- _ /\ _ => split
                  | _ => lia
                  | _ => apply Z.div_le_lower_bound
                  | _ => apply Z.div_lt_upper_bound
                  | _ => apply Z.div_le_upper_bound
                  end].
  

  Hint Unfold equivalent exec Machine.exec size spec value.
  Hint Unfold sum sum'.
  
  Lemma sums_equiv : sum == sum'.
  Proof.
    repeat match goal with
           | _ => progress (intros; autounfold)
           | _ => progress autorewrite with push_map push_mapt push_nth_default
           | _ => progress pose_valid_context_range
           | |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia
           end.
    rewrite Z.shiftr_div_pow2, Z.pow_1_r by lia.
    rewrite !Z.mod_small by solve_zrange.
    reflexivity.
  Qed.
End Examples.
    
    
    