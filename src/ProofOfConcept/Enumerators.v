Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Optimizer.Util.Deciders.
Require Import Optimizer.Util.ListUtil.
Require Import Optimizer.Util.Tactics.
Require Import Optimizer.Util.ZUtil.
Require Import Optimizer.AbstractMap.
Require Import Optimizer.Machine.
Require Import Optimizer.MachineProofs.
Require Import Optimizer.System.
Require Import Optimizer.ProofOfConcept.CostModel.
Require Import Optimizer.ProofOfConcept.Maps.
Import ListNotations.
Local Open Scope Z_scope.
Import Machine.Machine.

Section Enumerators.
  Context `{instrt : instr_impl}.
  Context (instr_cost : instruction -> nat) (instr_size : instruction -> Z) (cost : program -> nat).
  Existing Instance reg_mapt. Existing Instance flag_mapt.
  Existing Instance reg_enum. Existing Instance flag_enum. Existing Instance instr_enum.
  Hint Resolve reg_eq_dec flag_eq_dec instr_eq_dec : deciders.
  
  (* strips away irrelevant details like swapping equivalent
    registers around. Eventually this will need to be a little more
    sophisticated as the cost model matures.  *)
  Definition abstract_program := list instruction.
  Fixpoint to_abstract (p : program)
    : abstract_program :=
    match p with
    | Ret _ => []
    | Instr i _ _ cont => i :: to_abstract cont
    end.

  Fixpoint enumerate_under_cost' (fuel max_cost : nat)
    : list abstract_program :=
    match fuel with
    | O => [ ]
    | S fuel' =>
      [] ::
         flat_map (fun i =>
                     if lt_dec i.(instr_cost) max_cost
                     then
                       List.map (cons i)
                                (enumerate_under_cost' fuel' (max_cost - i.(instr_cost)))
                     else []) enum
    end.
  Definition enumerate_under_cost max_cost :=
    enumerate_under_cost' max_cost max_cost.

  (* Note : don't compute this! For proofs only. *)
  Fixpoint enumerate_possible_maps {A B} {mapt : map_impl A}
           (default : B) (possible_values : A -> list B)
           (keys : list A)
    : list (map A B) :=
    match keys with
    | [] => [empty default]
    | k :: keys' =>
      flat_map
        (fun m =>
           List.map (fun v => update m k v) (possible_values k))
        (enumerate_possible_maps default possible_values keys')
    end.

  Definition enumerate_contexts :=
    enumerate_possible_maps
      0
      (fun r => Z.seq 0 (2^(register_size r)))
      enum.
  Definition enumerate_flag_contexts :=
    enumerate_possible_maps
      false
      (fun _ => [true; false])
      enum.

  Definition enumerate_argument_values (max_const : Z)
    : list (register + Z) :=
    List.map inr (Z.seq 0 max_const) ++ List.map inl enum.
  Fixpoint enumerate_arguments (max_val : Z) (n : nat) :=
    match n with
    | O => [ [] ]
    | S n' =>
      List.flat_map
        (fun x =>
           List.map (cons x) (enumerate_arguments max_val n'))
        (enumerate_argument_values max_val)
    end.
  Fixpoint enumerate_concrete (ap : abstract_program)
    : list program :=
    match ap with
    | [] => List.map Ret enum
    | i :: ap' =>
      List.flat_map
        (fun cont =>
           List.flat_map
             (fun args =>
                List.map
                  (fun rd => Instr i rd args cont) enum)
             (enumerate_arguments
                (2 ^ instr_size i)
                i.(num_source_regs)))
        (enumerate_concrete ap')
    end.
  Definition enumerate_programs_under_cost max_cost :=
    List.flat_map enumerate_concrete
                  (enumerate_under_cost max_cost).

  Definition enumerate_under_cost_with_condition
             (condition : program -> bool) max_cost  : list program :=
    (List.filter condition (enumerate_programs_under_cost max_cost)).

  Section EnumeratorProofs.
    Context (instr_cost_pos : forall i, (0 < instr_cost i)%nat)
            (cost_Ret : forall r, cost (Ret r) = 0%nat)
            (cost_Instr :
               forall i rd args cont,
                 (cost (Instr i rd args cont) = cost cont + instr_cost i)%nat)
            (precondition_instr_size :
               forall i rd args x,
                 precondition i rd args ->
                 In (inr x) args ->
                 0 <= x < 2^instr_size i)
            (precondition_num_source_regs :
               forall i rd args,
                 precondition i rd args ->
                 length args = num_source_regs i)
            (precondition_dec :
               forall i rd args,
                 {precondition i rd args} + {~ precondition i rd args})
            (register_size_pos : forall r, 0 < register_size r).

    Lemma enumerate_under_cost'_complete :
      forall p max_cost fuel,
        (max_cost <= fuel)%nat ->
        (cost p < max_cost)%nat ->
        In (to_abstract p) (enumerate_under_cost' fuel max_cost).
    Proof.
      induction p; intros; (destruct fuel; [lia|]); [ cbn; tauto | ].
      cbn [to_abstract enumerate_under_cost' flat_map].
      apply in_cons, in_flat_map.
      exists i. pose proof (instr_cost_pos i).
      split; [ apply enum_complete | ].
      rewrite cost_Instr in *.
      break_match; [ | lia ].
      apply in_map, IHp; lia.
    Qed.
    Lemma enumerate_under_cost_complete p max_cost :
      (cost p < max_cost)%nat ->
      In (to_abstract p) (enumerate_under_cost max_cost).
    Proof. intros; apply enumerate_under_cost'_complete; lia. Qed.

    Lemma enumerate_under_cost'_bound :
      forall p max_cost fuel,
        (0 < max_cost <= fuel)%nat ->
        In (to_abstract p) (enumerate_under_cost' fuel max_cost) ->
        (cost p < max_cost)%nat.
    Proof.
      induction p; intros; (destruct fuel; [lia|]); [ rewrite cost_Ret; lia | ].
      cbn [to_abstract enumerate_under_cost' flat_map] in *.
      repeat match goal with
             | H : In _ (_ :: _) |- _ => inversion H; clear H; try discriminate
             | H : In _ [] |- _ => inversion H
             | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
             | H : In _ (flat_map _ _) |- _ => rewrite in_flat_map in H;
                                                 destruct H as [? [? ?] ]
             | H : In _ (List.map _ _) |- _ => rewrite in_map_iff in H;
                                                 destruct H as [? [? ?] ]
             | _ => rewrite cost_Instr
             | _ => progress break_match
             end.
      specialize (instr_cost_pos i).
      specialize (IHp (max_cost - instr_cost i)%nat fuel ltac:(lia) ltac:(auto)).
      lia.
    Qed.
    Lemma enumerate_under_cost_bound p max_cost :
      (0 < max_cost)%nat ->
      In (to_abstract p) (enumerate_under_cost max_cost) ->
      (cost p < max_cost)%nat.
    Proof.
      cbv [enumerate_under_cost]; intros.
      apply enumerate_under_cost'_bound with (fuel:=max_cost); auto; lia.
    Qed.

    Lemma enumerate_possible_maps_complete'
          A B mapt default possible_values keys
          (key_dec : forall k1 k2 : A, {k1 = k2} + {k1 <> k2}):
      forall m,
        (forall k, In (get m k) (possible_values k)) ->
        exists m',
          (forall k, In k keys -> get m k = get m' k) /\
          In m' (@enumerate_possible_maps A B mapt default possible_values keys).
    Proof.
      intros; induction keys as [|k ?];
        cbn [enumerate_possible_maps].
      { intros. exists (empty default). split.
        { intros.
          match goal with H : _ |- _ =>
                          apply in_nil in H; contradiction H
          end. }
        { apply in_eq. } }
      { intros. destruct IHkeys as [m' [? ?]].
        exists (update m' k (get m k)). split.
        { intro k2; destruct (key_dec k k2); [|destruct 1];
            subst; autorewrite with push_mapt; auto; congruence. }
        { apply in_flat_map. exists m'. auto using in_map. } }
    Qed.

    Lemma enumerate_possible_maps_complete
          A B (mapt : map_impl A) default possible_values keys
          (map_equiv :
             forall m1 m2 : map A B,
               (forall a, get m1 a = get m2 a) ->
               m1 = m2)
          (key_dec : forall k1 k2 : A, {k1 = k2} + {k1 <> k2}) :
      forall m,
        (forall k, In k keys) ->
        (forall k, In (get m k) (possible_values k)) ->
        In m (@enumerate_possible_maps A B mapt default possible_values keys).
    Proof.
      intros.
      destruct (enumerate_possible_maps_complete' A B mapt default possible_values keys key_dec _ ltac:(eassumption)) as [m' [Hget HIn]].
      replace m with m' by auto using eq_sym. auto.
    Qed.

    Section with_reg_map.
      Context (reg_map_equiv :
                 forall B (m1 m2 : map register B),
                   (forall a, get m1 a = get m2 a) ->
                   m1 = m2).
      Lemma enumerate_contexts_complete ctx :
        valid_context ctx ->
        In ctx enumerate_contexts.
      Proof.
        intros; apply enumerate_possible_maps_complete; auto with deciders; [ ].
        intro r. pose proof (valid_context_range ctx r ltac:(auto)).
        apply Z.in_seq; lia.
      Qed.
    End with_reg_map.

    Section with_flag_map.
      Context (flag_map_equiv :
                 forall B (m1 m2 : map flag B),
                   (forall a, get m1 a = get m2 a) ->
                   m1 = m2).
      Lemma enumerate_flag_contexts_complete fctx :
        In fctx enumerate_flag_contexts.
      Proof.
        intros; apply enumerate_possible_maps_complete; auto with deciders; [ ].
        intro f; destruct (get fctx f); cbn; tauto.
      Qed.
      Instance fctx_enum : enumerator (map flag bool).
      Proof. econstructor. apply enumerate_flag_contexts_complete. Defined.
    End with_flag_map.

    Lemma enumerate_argument_values_complete i rd args :
      precondition i rd args ->
      Forall (fun a => In a (enumerate_argument_values (2 ^ instr_size i))) args.
    Proof.
      cbv [enumerate_argument_values]; intros.
      apply Forall_forall; intros.
      apply in_or_app.
      match goal with
      | a : register + Z |- _ => destruct a; [right|left]
      end.
      { apply in_map; auto. }
      { pose proof (precondition_instr_size _ _ _ _ ltac:(eassumption) ltac:(eassumption)).
        apply in_map, Z.in_seq; lia. }
    Qed.

    Lemma enumerate_arguments_complete' i rd args :
      precondition i rd args ->
      In args
         (enumerate_arguments (2 ^ (instr_size i)) (length args)).
    Proof.
      intro Hpre; apply enumerate_argument_values_complete in Hpre.
      induction args as [|a args]; intros; list_cleanup.
      { cbn; tauto. }
      { cbn [enumerate_arguments].
        apply in_flat_map. exists a.
        auto using in_map. }
    Qed.

    Lemma enumerate_arguments_complete i rd args :
      precondition i rd args ->
      In args
         (enumerate_arguments (2 ^ i.(instr_size))
                              (i.(num_source_regs))).
    Proof.
      intros.
      erewrite <-precondition_num_source_regs by eauto.
      eauto using enumerate_arguments_complete'.
    Qed.

    Lemma enumerate_concrete_complete p:
      valid p ->
      In p (enumerate_concrete (to_abstract p)).
    Proof.
      induction p; intros; cbn [to_abstract enumerate_concrete];
        repeat match goal with
               | _ => inversion_valid
               | _ => apply in_flat_map;
                        eexists; split; [ solve [eauto using enumerate_arguments_complete] | ]
               | _ => apply in_map_iff;
                        eexists; split; [ solve [eauto] | ]
               | _ => solve [auto] 
               end.
    Qed.
    Lemma enumerate_concrete_to_abstract p :
      forall x,
        In p (enumerate_concrete x) ->
        x = to_abstract p.
    Proof.
      induction p; destruct x; cbn [to_abstract enumerate_concrete];
        repeat match goal with
               | _ => progress intros
               | H : In _ (_ :: _) |- _ => inversion H; clear H; try discriminate
               | H : In _ [] |- _ => inversion H
               | H : ?f _ _ = ?f _ _ |- _ => progress (inversion H; clear H; subst)
               | H : ?f _ _ _ _ = ?f _ _ _ _ |- _ => progress (inversion H; clear H; subst)
               | H : In _ (flat_map _ _) |- _ => rewrite in_flat_map in H;
                                                   destruct H as [? [? ?] ]
               | H : In _ (List.map _ _) |- _ => rewrite in_map_iff in H;
                                                   destruct H as [? [? ?] ]
               | _ => congruence
               end.
      rewrite (IHp x); auto.
    Qed.

    Lemma enumerate_programs_under_cost_complete p c :
      valid p ->
      (cost p < c)%nat ->
      In p (enumerate_programs_under_cost c).
    Proof.
      intros; cbv [enumerate_programs_under_cost].
      apply in_flat_map. exists (to_abstract p).
      auto using enumerate_under_cost_complete, enumerate_concrete_complete.
    Qed.

    Lemma enumerate_programs_under_cost_bound p c :
      (0 < c)%nat ->
      In p (enumerate_programs_under_cost c) ->
      (cost p < c)%nat.
    Proof.
      cbv [enumerate_programs_under_cost].
      rewrite in_flat_map. destruct 2 as [? [? ?]].
      repeat match goal with
             | H : _ |- _ => apply enumerate_concrete_to_abstract in H; subst
             | H : _ |- _ => apply enumerate_under_cost_bound in H; lia
             end.
    Qed.

    Lemma enumerate_programs_under_cost_complete_alt p c :
      ~ In p (enumerate_programs_under_cost c) ->
      (~ valid p) \/ (~ (cost p < c))%nat.
    Proof.
      intros; pose proof (enumerate_programs_under_cost_complete p c).
      apply Decidable.not_and.
      { destruct (valid_dec p); [left | right]; tauto. }
      { destruct 1; intros; tauto. }
    Qed.

    Lemma enumerate_under_cost_with_condition_complete cond max_cost p :
      cond p = true -> valid p -> (cost p < max_cost)%nat ->
      In p (enumerate_under_cost_with_condition cond max_cost).
    Proof.
      cbv [enumerate_under_cost_with_condition]; intros.
      apply filter_In.
      split; repeat break_match; try tauto;
        auto using enumerate_programs_under_cost_complete.
    Qed.
    Lemma enumerate_under_cost_with_condition_sound cond max_cost p :
      In p (enumerate_under_cost_with_condition cond max_cost) ->
      cond p = true.
    Proof.
      cbv [enumerate_under_cost_with_condition].
      rewrite filter_In.
      repeat break_match; intros;
        repeat match goal with H : _ /\ _ |- _ => destruct H end;
        auto; congruence.
    Qed.
    Lemma enumerate_under_cost_with_condition_bound cond max_cost p :
      (0 < max_cost)%nat ->
      In p (enumerate_under_cost_with_condition cond max_cost) ->
      (cost p < max_cost)%nat.
    Proof.
      cbv [enumerate_under_cost_with_condition].
      rewrite filter_In.
      repeat break_match; intros;
        repeat match goal with H : _ /\ _ |- _ => destruct H end.
      auto using enumerate_programs_under_cost_bound.
    Qed.
    Lemma enumerate_under_cost_with_condition_zero cond :
      enumerate_under_cost_with_condition cond 0 = [].
    Proof. reflexivity. Qed.
  End EnumeratorProofs.
End Enumerators.
