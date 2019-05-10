Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.System.
Require Import Optimizer.Machine.
Local Open Scope Z_scope.
Import Machine.
Import ListNotations.

Module Graphs.
  Section Graphs.
    Context `{instrt : instr_impl}.
    Context (instr_size : instruction -> Z) (instr_size_pos : forall i, 0 < i.(instr_size)).
    Context (instr_cost : instruction -> nat).
    Existing Instance reg_mapt. Existing Instance flag_mapt.
    Existing Instance reg_enum. Existing Instance flag_enum.

    Inductive node : Type :=
    | lvar : positive -> node (* the positive is an identifier *)
    | lconst : Z -> node
    | op : instruction -> list nat -> list nat -> node
    .
    Definition graph : Type := list node.

    (* returns the index of the argument a within the new graph, which
    is the same as the old but with a constant appended to the end if
    a is constant *)
    Definition to_graph_arg (ctx : map register nat) (a : register + Z)
               (state : list nat * graph) : list nat * graph :=
      match a with
      | inl r => (get ctx r :: fst state, snd state)
      | inr z => (length (snd state) :: fst state, snd state ++ [lconst z])
      end.
    Fixpoint to_graph' (ctx : map register nat) (fctx : map flag nat)
             (g : graph) (p : program) : graph :=
      match p with
      | Ret r => skipn (get ctx r) g
      | Instr i rd args cont =>
        let flags := List.map (get fctx) i.(flags_read) in
        let args_g' := fold_right (to_graph_arg ctx) ([], g) args in
        let ctx' := fold_right (fun r ctx => update ctx r (S (get ctx r))) ctx enum in
        let fctx' := fold_right (fun f fctx => update fctx f (S (get fctx f))) fctx enum in
        let ctx'' := update ctx' rd 0%nat in
        let fctx'' := fold_right (fun f fctx => update fctx f 0%nat) fctx' i.(flags_written) in
        to_graph' ctx'' fctx'' (op i (fst args_g') flags :: snd args_g') cont
      end.

    Definition init_ctx {T} {mapt : map_impl T} {enumT : enumerator T} (start : nat) : map T nat :=
      fold_right (fun ti ctx => update ctx (fst ti) (snd ti))
                 (empty 0%nat)
                 (combine enum (seq start (length enum))).
    Definition to_graph :=
      let nregs := length (@enum register _) in
      let nflags := length (@enum flag _) in
      to_graph' (init_ctx 0) (init_ctx nregs) (List.map (fun i => lvar (Pos.of_nat i)) (seq 1 (nregs + nflags))).
    Definition rep p t : Prop := to_graph p = t.

    Definition egraph : Type := list (node * list nat).
    Definition to_egraph (g : graph) : egraph := List.map (fun n => (n, [])) g.

    Definition get_node (g : graph) (i : nat) : node := nth_default (lconst 0) g i.
    Definition eget_node (e : egraph) (i : nat) : node := fst (nth_default (lconst 0, []) e i).
    Definition eget_node_and_graph (e : egraph) (i : nat) : (node * egraph) := (eget_node e i, skipn i e).

    Definition extend_root (e : egraph) (i : nat) :=
      match e with
      | [] => []
      | (n, eqclass) :: e' => (n, i :: eqclass) :: e'
      end.

    Fixpoint top_level' (pos : nat) (hit_list : list nat) (e : egraph) : list nat :=
      match e with
      | [] => []
      | (n, eqclass) :: e' =>
        if in_dec Nat.eq_dec pos hit_list
        then pos :: top_level' (S pos) (hit_list ++ List.map (Nat.add pos) eqclass) e'
        else top_level' (S pos) hit_list e'
      end.
    Definition top_level (start : nat) := top_level' 0%nat [start].

    Definition adjust (idx : nat) (args : list nat) :=
      List.map (fun a => if lt_dec a idx then a else (a - 1)%nat) args.
    Fixpoint try_remove_node (g : graph) (idx : nat) : option graph :=
      match idx with
      | O => Some (tl g)
      | S idx' =>
        match g with
        | [] => Some []
        | op i args flags :: g' =>
          if in_dec Nat.eq_dec idx' args
          then None
          else if in_dec Nat.eq_dec idx' flags
               then None
               else option_map
                      (cons (op i (adjust idx' args) (adjust idx' flags)))
                      (try_remove_node g' idx')
        | n :: g' => option_map (cons n) (try_remove_node g' idx')
        end
      end.
    Fixpoint try_remove_enode (e : egraph) (idx : nat) : option egraph :=
      match idx with
      | O => Some (tl e)
      | S idx' =>
        match e with
        | [] => None 
        | (op i args flags, eqclass) :: e' =>
          if in_dec Nat.eq_dec idx' args
          then None
          else if in_dec Nat.eq_dec idx' flags
               then None
               else if in_dec Nat.eq_dec idx' eqclass
                    then None
                    else option_map
                           (cons (op i (adjust idx' args) (adjust idx' flags), adjust idx' eqclass))
                           (try_remove_enode e' idx')
        | n :: e' => option_map (cons n) (try_remove_enode e' idx')
        end
      end.
    
    (* Proof strategy for prune: Just prove that try_remove_node is
    always safe and don't bother proving that there's no dead code
    left once you're done *)
    Definition prune (g : graph) :=
      fold_right (fun i g =>
                    match try_remove_node g i with
                    | Some g' => g'
                    | None => g
                    end) g (seq 1 (length g)).
    Definition eprune (g : egraph) :=
      fold_right (fun i g =>
                    match try_remove_enode g i with
                    | Some g' => g'
                    | None => g
                    end) g (seq 1 (length g)).

    Context {pos_mapt : map_impl positive}.
    Context {pos_map_eqb : forall {B}, (B -> B -> bool) -> map positive B -> map positive B -> bool}.
    
    Fixpoint match_expr'
             (possible_assignments : list (map positive (option nat)))
             (g : graph) (* graph we're matching *)
             (pos : nat) (* current position in top-level egraph (used for assignments) *)
             (countdown : nat) (* number of steps in e until we reach our target node *)
             (e : egraph)
      : list (map positive (option nat)) :=
      match e with
      | [] => []
      | (n, eqclass) :: e' =>
        match countdown with
        | S countdown' => match_expr' possible_assignments g (S pos) countdown' e'
        | O =>
          match g, n with
          | [], _ => possible_assignments
          | lvar id :: _, _ =>
            flat_map
              (fun assignment =>
                 match get assignment id with
                 | None => [update assignment id (Some pos)]
                 | Some i => if Nat.eqb i pos then [assignment] else []
                 end)
              possible_assignments
          | lconst z :: _, lconst z' => if Z.eqb z z' then possible_assignments else []
          | op i args flags :: _, op i' args' flags' =>
            if instr_eq_dec i i'
            then
              fold_right
                (fun g'_eqclass possible_assignments =>
                   flat_map
                     (fun idx => match_expr' possible_assignments (fst g'_eqclass) (S pos) idx e')
                     (snd g'_eqclass))
                possible_assignments
                (combine (List.map (fun idx => skipn (S idx) g) args)
                         (List.map (fun idx => top_level idx e') args'))
            else []
          | _, _ => []
          end
        end
      end.
    Definition match_expr (g : graph) (e : egraph) :=
      match_expr' [empty None] g 0%nat 0%nat e.

    (* TODO: move *)
    Definition bind {A B} (f : A -> option B) (x : option A) : option B :=
      match x with
      | Some a => f a
      | None => None
      end.
    
    Definition new_position (assignment : map positive (option nat)) (offset: nat) (g : graph) (idx : nat)
      : option nat :=
      match get_node g idx with
      | lvar id => option_map (Nat.add (offset - 1)) (get assignment id)
      | _ => Some idx
      end.
    Definition new_positions (assignment : map positive (option nat)) (offset: nat) (g : graph) :
      list nat -> option (list nat) :=
             fold_right
               (fun idx oargs' =>
                  bind
                    (fun args' =>
                       option_map
                         (fun idx' => idx' :: args')
                         (new_position assignment offset g idx))
                    oargs')
               (Some []).
    Fixpoint assign_vars (assignment : map positive (option nat)) (offset : nat) (g : graph) : option graph :=
      match g with
      | [] => Some []
      | lvar id :: g' => option_map (cons (lconst 0)) (assign_vars assignment offset g')
      | lconst z :: g' => option_map (cons (lconst z)) (assign_vars assignment offset g')
      | op i args flags :: g' =>
        bind 
          (fun rec =>
             bind
               (fun args' =>
                  option_map
                    (fun flags' => op i args' flags' :: rec)
                    (new_positions assignment (length rec + offset) g' flags))
               (new_positions assignment (length rec + offset) g' args))
          (assign_vars assignment offset g')
      end.

    Definition add_branch' (rule_rhs : graph) assignment (offset : nat) (e : egraph) : nat * egraph :=
      match assign_vars assignment offset rule_rhs with
      | Some g =>
        let b := to_egraph g in
        ((offset + length b)%nat, extend_root (b ++ e) (length b - 1))
      | None => (0%nat, e)
      end.
    (* In some cases, the rule-match might just say two parts of
    the existing graph are equal -- in which case g will be only a
    variable and the correct behavior is to add the corresponding nat
    to the equivalence class of the root. *)
    Definition add_branch (rule_rhs : graph) assignment (offset : nat) (e : egraph) : nat * egraph :=
      match rule_rhs with
      | lvar id :: _ =>
        match get assignment id with
        | Some n => (0%nat, extend_root e (n + offset - 1))
        | None => (0%nat, e)
        end
      | _ => add_branch' rule_rhs assignment offset e
      end.
    (* TODO : eventually, want to match rhs and exclude, or perhaps go through all egraphs and remove duplicates *)
    Definition apply_rule (rule_lhs : graph) (rule_rhs : graph) (e : egraph) : nat * egraph :=
      fold_right (fun a off_out => add_branch rule_rhs a (fst off_out) (snd off_out))
                      (0%nat, e) (match_expr rule_lhs e).

    Definition shift_front (n : node) (eqclass : list nat) (offset : nat) : node * list nat :=
      match n with
        | op i args flags =>
          let args'    := List.map (Nat.add offset) args    in
          let flags'   := List.map (Nat.add offset) flags   in
          let eqclass' := List.map (Nat.add offset) eqclass in
          (op i args' flags', eqclass')
        | _ =>
          let eqclass' := List.map (Nat.add offset) eqclass in
          (n, eqclass')
      end.
    Fixpoint repeat_apply_rule (fuel : nat) (rule_lhs rule_rhs : graph) (e : egraph) : nat * egraph :=
      match fuel with
      | O => (0%nat, e)
      | S fuel' =>
        match e with
        | [] => (0%nat, [])
        | (n, eqclass) :: e' =>
          let '(offset, e') := repeat_apply_rule fuel' rule_lhs rule_rhs e' in
          apply_rule rule_lhs rule_rhs (shift_front n eqclass offset :: e')
        end
      end.

    (* Putting it all together... *)
    Fixpoint repeat_apply_rules (fuel : nat) (rules : list (graph * graph)) (e : egraph)
      : egraph :=
      eprune (fold_right (fun r e => snd (repeat_apply_rule fuel (fst r) (snd r) e)) e rules).
    
  End Graphs.
End Graphs.


Module PositiveMaps.
    Definition pos_map' {B : Type} : Type := list (positive * B).
    Definition pos_map {B : Type} : Type := B * @pos_map' B.

    Fixpoint get' {B} (d : B) (m : pos_map') (p : positive) : B :=
      match m with
      | [] => d
      | pb :: m' =>
        if Pos.eqb (fst pb) p then snd pb else get' d m' p
      end.
    Definition get {B} (m : pos_map) (p : positive) : B :=
      get' (fst m) (snd m) p.

    Definition update {B} (m : pos_map) (p : positive) (v : B) :=
      (fst m, (p,v) :: snd m).

    Definition empty {B} (default : B) : pos_map := (default, []).

    Lemma get_empty B (d : B) p : get (empty d) p = d.
    Proof. reflexivity. Qed.
    
    Lemma get_update_eq B p (b : B) (m : pos_map) : get (update m p b) p = b.
    Proof. cbv [get get' update]. cbn [fst snd]. rewrite Pos.eqb_refl. reflexivity. Qed.
    Lemma get_update_neq B p1 p2 (b : B) (m : pos_map) : p1 <> p2 -> get (update m p1 b) p2 = get m p2.
    Proof. rewrite <-Pos.eqb_neq. intros; cbv [get get' update]. cbn [fst snd].
           destruct (Pos.eqb p1 p2); congruence. Qed.

    Instance pos_mapt : map_impl positive.
    Proof.
      apply Build_map_impl with (get:=@get) (update:=@update) (empty:=@empty).
      { apply get_empty. }
      { apply get_update_eq. }
      { apply get_update_neq. }
    Defined.
End PositiveMaps.
Existing Instance PositiveMaps.pos_mapt.


Require Import ProofOfConcept.Glue.
Require Import ProofOfConcept.Registers.
Import Registers.
Import Instructions.
Import Graphs.
Definition exg : graph := Eval vm_compute in (to_graph (Instr ADD32 r0 [inl r0; inr 0] (Ret r0))).
Print exg.
(*
[op ADD32 [0%nat; 9%nat] []; lvar 1; lvar 2; lvar 3; lvar 4; lvar 5; lvar 6; lvar 7; lvar 8; lvar 9; lconst 0]
*)

(* ADD r0 r0 r0
       \\________________
        \                \
         \           ADD r0 r0 0
          \_____    _____/
                \  /
          ADD r0 r0 r1
 *)
Definition exp : program :=
  Instr ADD32 r0 [inl r0;inl r0]
        (Instr ADD32 r0 [inl r0; inr 0]
               (Instr ADD32 r0 [inl r0; inl r1] (Ret r0))).
Definition exe : egraph :=
  (* based on Eval vm_compute in (to_egraph (Graphs.to_graph exp)) *)
  [(*(op ADD32 [0%nat; 3%nat] [], []); *)
     (op ADD32 [0%nat; 10%nat] [], [0%nat]);
     (op ADD32 [2%nat; 2%nat] [], []);
     (lvar 1, []); (lvar 2, []); (lvar 3, []);
       (lvar 4, []); (lvar 5, []); (lvar 6, []);
         (lvar 7, []); (lvar 8, []); (lvar 9, []);
           (lconst 0, [])].
Definition exr_lhs : graph := [op ADD32 [0%nat; 1%nat] []; lvar 1%positive; lconst 0].
Definition exr_rhs : graph := [op MUL64 [0%nat; 1%nat] []; lvar 1%positive; lconst 1].
Definition exr_rhs' : graph := [lvar 1%positive].

Definition exm := match_expr exg exe.
Eval vm_compute in exm.
Eval vm_compute in (add_branch exr_rhs (None, [(1%positive, Some 1%nat)]) 0%nat exe).
Definition exa := snd (apply_rule exg exr_rhs exe).
Eval vm_compute in (eprune exa).
Definition exa' := snd (repeat_apply_rule 50 exr_lhs exr_rhs' exa).
Eval vm_compute in exa'.
Eval vm_compute in (eprune exa').

Definition rules := [(exr_lhs, exr_rhs); (exr_lhs, exr_rhs')].
Eval vm_compute in (repeat_apply_rules 10 rules exe).


(*
= [(op MUL64 [1%nat; 0%nat] [], [1%nat]); (lconst 1, []); (op ADD32 [0%nat; 2%nat] [], [0%nat]);
       (op ADD32 [0%nat; 0%nat] [], []); (lvar 3, []); (lconst 0, [])]


MUL64    X  #1
 \       |
  \      | 
   \     |
   ADD32 X  #0
    \    |
     \   |
      \  |
      ADD32 $v3 $v3


*)