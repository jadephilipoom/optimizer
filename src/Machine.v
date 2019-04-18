Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.System.
Local Open Scope Z_scope.

Module Machine.
  Section Machine.
    Context `{instrt : instr_impl}.
    Existing Instance reg_mapt. Existing Instance flag_mapt.
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

  Infix "==" := equivalent (at level 40).
  (* TODO: these don't work for parsing and I've no idea why *)
  Notation "i % rd x ; p" := (Instr i rd (x :: nil) p) (at level 100, p at level 200, format "i  % rd  x ; '//' p").
  Notation "i % rd x y ; p" := (Instr i rd (x :: y :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y ; '//' p").
  Notation "i % rd x y z ; p" := (Instr i rd (x :: y :: z :: nil) p) (at level 100, p at level 200, format "i  % rd  x  y  z ; '//' p").
End Machine.