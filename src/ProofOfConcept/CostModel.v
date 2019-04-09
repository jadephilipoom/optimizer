Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Optimizer.Machine.

Module CostModel.
  Import Machine.
  Section CostModel.
    Context {register flag instruction : Set}
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
