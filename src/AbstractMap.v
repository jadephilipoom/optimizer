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
Hint Rewrite @get_update_eq @get_empty @get_update_neq using congruence :  push_mapt.
