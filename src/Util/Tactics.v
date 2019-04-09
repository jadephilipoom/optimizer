Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  | H : context [match ?x with _ => _ end] |- _ => destruct x
  end.
Ltac destruction :=
  repeat match goal with
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : ?x = ?x |- _ => destruct H
         end.