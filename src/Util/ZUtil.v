Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

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