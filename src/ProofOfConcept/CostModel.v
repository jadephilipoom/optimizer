Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Optimizer.Machine.
Require Import Optimizer.System.

Module CostModel.
  Import Machine.
  Section CostModel.
    Context `{instrt : instr_impl} {instr_cost : instruction -> nat}.
    Fixpoint cost (p : program) : nat :=
      match p with
      | Ret r => 0
      | Instr i rd args cont => i.(instr_cost) + cost cont
      end.

    Section Proofs.
      Context (instr_cost_pos : forall i, (0 < instr_cost i)%nat).

      Lemma cost_of_instr_pos i rd args cont :
        (cost cont < cost (Machine.Instr i rd args cont))%nat.
      Proof. specialize (instr_cost_pos i). cbn [cost]. omega. Qed.
    End Proofs.
  End CostModel.
End CostModel.
