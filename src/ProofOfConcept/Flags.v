Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope Z_scope.

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

Section Proofs.
  Lemma all_flags_complete : forall f, In f Flags.all_flags.
  Proof. destruct f; cbn; tauto. Qed.
End Proofs.