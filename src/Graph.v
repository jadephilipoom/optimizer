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

    Inductive leaf : Type :=
    | lvar : positive -> leaf (* the positive is an identifier *)
    | lconst : Z -> leaf
    .
    Inductive tree : Type :=
    | Leaf : leaf -> tree
    | Node : instruction -> list tree -> list tree -> tree.

    Local Definition to_graph_arg (ctx : map register tree) (a : register + Z) : tree :=
      match a with
      | inl r => get ctx r
      | inr z => Leaf (lconst z)
      end.
    Fixpoint to_graph' (ctx : map register tree) (fctx : map flag tree) (p : program) : tree :=
      match p with
      | Ret r => get ctx r
      | Instr i rd args cont =>
        let node := Node i
                         (List.map (to_graph_arg ctx) args)
                         (List.map (get fctx) i.(flags_read)) in
        let fctx' := fold_right (fun f fctx  => update fctx f node) fctx i.(flags_written) in
        let ctx' := update ctx rd node in
        to_graph' ctx' fctx' cont
      end.
    Definition fill_vars {A} {A_mapt : map_impl A} {A_enum : enumerator A} (start : positive)
      : positive * map A tree :=
      fold_right (fun r im => ((fst im + 1)%positive, update (snd im) r (Leaf (lvar (fst im)))))
                 (1%positive, empty (Leaf (lconst 0))) enum.
    Definition to_graph : program -> tree :=
      let '(i, start_context) := fill_vars 1 in
      let '(i, start_flags) := fill_vars i in
      to_graph' start_context start_flags.

    Definition rep p t : Prop := to_graph p = t.

    Axiom candidates : program -> list tree. (* TODO *)
    Axiom cost : program -> nat.
    Axiom graph_max_cost : tree -> nat.
    Axiom graph_max_cost_correct :
      forall p t, rep p t -> (cost p <= graph_max_cost t)%nat.

    (* TODO: this statement would be less awkward if we required p2 to
    be optimal, but optimal defn isn't in scope *)
    Lemma candidates_complete p1 p2 :
      equivalent p1 p2 ->
      (cost p2 < cost p1)%nat ->
      exists p3,
        (cost p3 <= cost p2)%nat /\  In (to_graph p3) (candidates p1).
    Proof.
      (* TODO *)
    Admitted.

    (* in an etree, every node is actually an equivalence class -- including leaves *)
    Inductive etree : Type :=
    | enode : list (leaf + (instruction * list etree * list etree)) -> etree
    .

    (* TODO: move *)
    Fixpoint map2 {A B C} (f : A -> B -> C) (la : list A) (lb : list B) :=
      match la, lb with
      | a :: la', b :: lb' =>
        f a b :: map2 f la' lb'
      | _, _ => nil
      end.
    Lemma map2_cons A B C f a b la lb :
      @map2 A B C f (a :: la) (b :: lb) = f a b :: map2 f la lb.
    Proof. reflexivity. Qed.
    Lemma map2_nil A B C f : @map2 A B C f nil nil = nil.
    Proof. reflexivity. Qed.
    Lemma map2_eq_combine A B C f la :
      forall lb,
        @map2 A B C f la lb = List.map (fun ab => f (fst ab) (snd ab)) (combine la lb).
    Proof.
      induction la; destruct lb; try reflexivity; [ ].
      rewrite map2_cons, IHla. reflexivity.
    Qed.

    Fixpoint to_partial_etree (t : tree) : etree :=
      match t with
      | Leaf l => enode (inl l :: nil)
      | Node i args flags =>
        enode
          (map2 (fun eargs eflags => inr (i, eargs :: nil, eflags :: nil))
                (List.map to_partial_etree args)
                (List.map to_partial_etree flags))
      end.


    (* How will I actually apply rules? *)
    (* a rule should map one (tree) subgraph to a single other (tree) subgraph *)
    (* then, we should insert the new subgraph by attaching the root and leaves *)

    (* okay, idea: recursively try to apply the rule and fail if you don't see all the stuff you want *)
    (* how do we tell where the leaves are supposed to connect between the left and right? *)

    (* What if the rules are egraphs? *)


    (* Sample input:
         
         rule -
              enode [ inr (ADD, [ enode [inl (Leaf (lconst 2))], enode [inl (Leaf (lconst 2))]], []);
                      inl (Leaf (lconst 4)), []) ]
         e -
              enode [ inr (ADD, [enode [inl (Leaf (lconst 4))];
                                 enode [ inr (ADD, [enode [inl (Leaf (lvar x))];
                                                    enode [inl (Leaf (lvar x))]]; []);
                                         inr (MUL, [enode [inl (Leaf (lvar x))];
                                                    enode [inl (Leaf (lconst 2))]]; [])]], []) ]
         out -
              enode [ inr (ADD, [enode [ inl (Leaf (lconst 4));
                                         inr (ADD, [enode [inl (Leaf (lconst 2))],
                                                    enode [inl (Leaf (lconst 2))]], [])];
                                 enode [ inr (ADD, [enode [inl (Leaf (lvar x))];
                                                    enode [inl (Leaf (lvar x))]]; []);
                                         inr (MUL, [enode [inl (Leaf (lvar x))];
                                                    enode [inl (Leaf (lconst 2))]]; [])]], []) ]

       
         rule -
              enode [ inr (ADD, [enode (Leaf (lvar i)), enode (Leaf (lvar j))], []);
                      inr (ADD, [enode (Leaf (lvar j)), enode (Leaf (lvar i))], []) ]
         e - 
              enode [ inr (ADD, [enode (Leaf (lvar x)), enode (Leaf (lvar y))], []) ]

         out - 
              enode [ inr (ADD, [enode (Leaf (lvar x)), enode (Leaf (lvar y))], []);
                      inr (ADD, [enode (Leaf (lvar y)), enode (Leaf (lvar x))], []) ]
         
         rule -
              enode [ inr (ADD, [enode (Leaf (lvar i)), enode (Leaf (lvar i))], []);
                      inr (MUL, [enode (Leaf (lvar i)), enode (Leaf (lconst 2))], []) ]
         e - 
              enode [ inr (ADD, [enode (Leaf (lvar x)), enode (Leaf (lvar x))], []) ]

         out - 
              enode [ inr (ADD, [enode (Leaf (lvar x)), enode (Leaf (lvar x))], []);
                      inr (MUL, [enode (Leaf (lvar x)), enode (Leaf (lconst 2))], []) ]

     *)

    (* one function that returns assignments if successful, other that extends tree *)
    

    (* if rules are egraphs :


       get_assignments assignments rule e :

       for (rel : leaf + (instruction * list etree * list etree)) in rule :
         for (eel : leaf + (instruction * list etree * list etree)) in e :
           if rel is leaf :
             if rel is constant:
                if eel is constant and constants are equal:
                   return assignments
                else:
                   continue
             elif rel is variable:
                 if assignments[id] is None or assignments[id] == eel :
                    return update assignments id eel
                 else:
                    continue
           if rel is node and eel is node:
              (ri, rargs, rflags) := rel (* rargs rflags : list etree *)
              (ei, eargs, eflags) := eel
              if ri == ei :
                 (* rargs/eargs and rflags/eflags are guaranteed to have same size *)
                 (* we need EVERY argument/flag etree in the rule to have some matching part with every argument/flag etree in the original *)
                 fold_right (fun ((rule', e') : etree) assignments =>
                              get_assignments assignments rule' e') assignments (combine rargs eargs ++ combine rflags eflags)

     extend assignments rule e :

     let rule' := substitute assignments rule
     etree_extend e rule'
     *)


    (* Note : as written, multiple occurences of the same rule will be rewritten over and over *)
    (* what we really need to do is only match instances if the rhs isn't already there *)

    Context {pos_mapt : map_impl positive}.
    Definition assignment : Type := map positive (option etree).


    Axiom elt_eqb : forall elt1 elt2 : leaf + (instruction * list etree * list etree), bool.
    Axiom elt_eq_dec : forall elt1 elt2 : leaf + (instruction * list etree * list etree),
        {elt1 = elt2} + {elt1 <> elt2}.
    About flat_map.

    (* the below probably will work but is *incredibly* nasty. *)
    (* Next steps would be to use the matcher to find all assignments
    for the rule lhs, eliminate the ones that also appear when you
    match the rhs, and then write a thing to extend the tree with the
    rhs instantiated with the remaining assignments *)
    
    (* TODO: think about how to set up the etree and the rewriting
    rules differently to make this matching less awful -- probably
    read some stuff *)

    (* TODO: we might eventually want things in terms of mathematical
    functions, so it might be good to do a structure that allows that *)

    (* ill-formed without fuel because Coq isn't smart enough to see under the combine/fold right *)
    Fixpoint match_tree'
             (depth : nat) (* fuel *)
             (all_assignments : list (map positive (option etree)))
             (t : tree) (e : etree)
      : list (map positive (option etree)) :=
      match depth with
      | O => nil
      | S depth' =>
        match e with
        | enode elts =>
          match t with
          | Leaf l =>
            match l with
            | lvar id =>
              flat_map (fun elt =>
                          flat_map
                            (fun assignment =>
                               match get assignment id return list (map positive (option etree)) with
                               | None => update assignment id (Some (enode elts)) :: nil
                               | Some e2 =>
                                 match e2 with
                                 | enode elts2 =>
                                   if in_dec elt_eq_dec elt elts2
                                   then [assignment]
                                   else nil
                                 end
                               end) all_assignments) elts
            | lconst z =>
              (* all the assignments are fine as long as a constant equal to z exists in elts *)
              match (find (fun elt => match elt with
                                      | inl (lconst z2) => Z.eqb z z2
                                      | _ => false
                                      end) elts) with
              | None => nil
              | Some _ => all_assignments
              end
            end
          | Node ri rargs rflags =>
            flat_map (fun elt =>
                        match elt with
                        | inl l => nil
                        | inr (i, args, flags) =>
                          if instr_eq_dec i ri
                          then
                            fold_right (fun te all_assignments =>
                                          match_tree' depth' all_assignments (fst te) (snd te))
                                       all_assignments (combine rargs args ++ combine rflags flags)
                          else nil
                        end) elts
          end
        end
      end.

    Fixpoint depth (e : etree) : nat :=
      match e with
      | enode elts =>
        fold_right (fun elt out =>
                      match elt with
                      | inl l => max 1 out
                      | inr (i, args, flags) =>
                        S (fold_right (fun t' => max (depth t'))
                                      (fold_right (fun t' => max (depth t'))
                                                  0%nat flags)
                                      args)
                      end) 0%nat elts
      end.

    Fixpoint get_assignments' assignments (rule_lhs : tree) (e : etree) : option (map positive etree) :=
      match e with
      | enode elts =>
        match rule_lhs with
        | Leaf l =>
        | Node ri rargs rflags =>
          fold_right (fun elt assignments =>
                        match elt with
                        | inl l => assignments
                        | inr (i, args flags) =>
                          if instr_eq_dec i ri
                          then
                            (* try following this node recursively -- if failure continue searching,
                               if success return *)
                          else assignments) assignments elts
        end
      end.
    
                      

    

    (* TODO: this will end up with lots of duplicates *)
    Definition etree_extend (e1 : etree) (e2 : etree) : etree :=
      match e1, e2 with
      | enode elts1, enode elts2 => enode (elts1 ++ elts2)
      end.
    
    Fixpoint apply_rule (rule : etree) (e : etree) : etree :=
      match rule with
      | enode relts =>
        match e with
        | enode eelts =>
          fold_right
            (fun relt e =>
               fold_right (fun eelt e =>
                             match relt, eelt with
                             | Leaf rl, Leaf el =>
                               if leaf_eq_dec rl el then extend e rule
                               
                   match rel with
                   | inr l =>
                     (* this matches anything in e that is the same kind of leaf *)
               

      
      match lhs with
      | Leaf l =>
        match e with
        | enode ets =>
          (* if we find the right kind of leaf we win *)
          
        
      match e with
      | enode ets =>
        (* look for the right lhs *)
        (* if we find the lhs, augment with the rhs somehow *)
        (* *)






    

    Fixpoint top_subgraphs (depth : nat) (e : etree) : list tree :=
      match depth with
      | O =>
        match e with
        | enode ets =>
          fold_right (fun et trees =>
                        match et with
                        | inl l => Leaf l :: trees
                        | _ => trees
                        end) nil ets
        end
      | S depth' =>
        match e with
        | enode ets =>
          fold_right (fun et trees =>
                        match et with
                        | inl l => trees
                        | inr (i, eargs, eflags) =>
                          (* 
                             get all size-depth' subgraphs of eargs, and all possible combinations thereof
                             

                           *)



                          
                          (fold_right (fun ea trees =>
                                         fold_right (fun a trees =>
                                                       fold_right (fun ef trees =>
                                                                     fold_right
                                                                       (fun f trees => Node i args flags :: trees)
                                                                       trees
                                                                       (List.map (top_subgraphs depth') eflags)
                                                                  )))
                                                                  eargs)
                                                    
                                       end.

    Fixpoint apply_rule
             (rule_depth : nat) (* depth of graph on lhs *)
             (rule_match : tree -> bool)
             (rule_result : tree -> tree)
             (e : etree) :=
      match e with
      | enode ets =>
        (* forall node things, gather all length-rule-depth sequences starting with i and check for a match, then substitute *)
        trees := fold_right (fun et trees =>
                               match et with
                               | inl l => trees
                                            | inr 
                               
        
      end.
      


    Definition etree_extend (e : etree) (t : tree) : etree :=
      match e with
      | enode ets =>
        match t with
        | Leaf l => (inl l :: ets)
        | Node i args flags =>
          
        
      end.
    
    
    Definition apply_equivalence (e : etree) (rule : tree -> tree)

    (* TODO: might need to add ways of computing constants *)
    Definition leaf_to_etree (l : leaf) : etree := enode (inl l :: nil).

    Fixpoint to_etree (t : tree) : etree :=
      match t with
      | Leaf l => leaf_to_etree l
      | Node i args flags =>
         

    Axiom equality_axioms : tree -> etree.

    
    (* TODO: graph system questions and problems to ponder

    - How should graphs keep track of flags?
      * As written values, same as results?
      * As part of the return value of an instruction, so that another
        instruction can read the same result multiple ways (the normal
        bits and the flag bits)? <--- done
    - What is a reasonably efficient way to enumerate potentially equivalent graphs?
      * Use a proven-complete and precomputed set of instruction
        substitutions + preconditions? (Would be pretty huge)
      * Use a proven-complete set of arithmetic axioms?
      * Use some proven axioms to *eliminate* branches?


      Ultimate goal:
        We need to eventually prove that, given two programs p1 and
        p2, if p1 and p2 are equivalent but p2 is faster than p1, then
        there exists p3 in (candidates p1) such that p3 is at least as
        fast as p2.

     *)


    (* Some potential rules to help with graph enumerating:

       - assuming we have precomputed the fastest versions of very
         short snippets, then a partially-complete graph with the
         first part equal to the original and the second part of the
         original very small can be completed with only the
         precomputed snippet
       - in general, if we *ever* have one of the precomputed snippets
         in a graph, we can replace it
       - this would immediately take care of the very small programs
       - what about larger ones?
         * well, we'd 


    *)

    
    Inductive graph_equivalent : tree -> tree -> Prop :=
    | equiv_Leaf : forall l, graph_equivalent (Leaf l) (Leaf l) 
    | equiv_Node :
        forall i args1 args2 flags1 flags2,
          Forall2 graph_equivalent args1 args2 ->
          Forall2 graph_equivalent flags1 flags2 ->
          graph_equivalent (Node i args1 flags1) (Node i args2 flags2)
    .


    
    (* Trees with annotated leaves *)
    Inductive atree (regA constA nodeA : Type) : Type :=
    | aLeaf_reg : regA -> atree regA constA
    | aLeaf_const : constA -> atree regA constA
    | aNode : instruction -> list (atree regA constA) -> atree regA constA.

    Print exec.
    Fixpoint exec_atree (start_ctx : map register Z) (t : atree register Z) (fctx : map flag bool) : Z :=
      match t with
      | aLeaf_reg r => get ctx r
      | aLeaf_const z => z
      | aNode i args =>
        let args' := List.map (fun a => exec_atree start_ctx a fctx) args in
        let result := spec i args' (get fctx) in
        let ctx' := update ctx 
        

    (* 
- Given a list of start values, we can form an atree by returning the
  atree and number of start values used in recursive calls.
- We can also execute atrees if they have registers/constants as their annotation, or even better Z for both
- We can convert programs to atrees and prove the atree execution equals the program execution -- although we will probably have to do this by comparing contexts.

Bigger question:
Should programs have explicit return values?
 *)
    
    

    Lemma Ret_equiv r r0 :
      Ret r == Ret r0 ->
      r = r0.
    Admitted.
    Lemma to_graph'_equiv p1 p2 :
      equivalent p1 p2 ->
      forall tctx,
        to_graph' tctx p1 = to_graph' tctx p2.
    Proof.
      induction p1; destruct p2.
      { intro Heq; intros; apply Ret_equiv in Heq.
        subst; intros. reflexivity. }
      { intro Heq; intros; cbv [equivalent] in Heq.
        cbn [exec] in Heq.
        cbn.
      P 
      induction 1; intros.
      

      
      induction p1; cbn [to_graph'].
      { intros Hequiv ctx; repeat intro.
        destruct p2.
        2 : { cbn in Hequiv.
        specialize (Hequiv 
        destruct p2; inversion 1.
        repeat intro. cbn [exec]. admit. }
      { repeat intro.
        destruct p2.
        cbn [to_graph'] in H.
        cbn [exec].
        cbv [equivalent] in IHp1.
        apply IHp1.


    (* Enumerate potentially equivalent graphs under cost *)

    (* First, we need to decide under what conditions a particular
    sequence of instructions could equal another *)
    Context (equivalence_conditions :
               graph -> graph -> list (Z -> Prop)).
    



    

    Inductive T : Type :=
    | Leaf_reg : (register -> Prop) -> T
    | Leaf_const : (Z -> Prop) -> T
    | Tree : instruction -> list T -> T.

    Inductive valid : Z -> T -> Prop :=
    | valid_leaf_reg :
        forall sz pre,
          valid sz (Leaf_reg pre)
    | valid_leaf_const :
        forall sz pre,
          valid sz (Leaf_const pre)
    | valid_tree :
        forall sz i args,
          length args = i.(num_source_regs) ->
          i.(instr_size) <= sz ->
          Forall (valid i.(instr_size)) args ->
          valid sz (Tree i args)
    .

    Inductive rep_arg : T -> (register + Z) -> Prop :=
    | rep_leaf_reg : forall sz (pre : register -> Prop) r,
        register_size r = sz ->
        pre r ->
        rep_arg (Leaf_reg sz pre) (inl r)
    | rep_leaf_const : forall sz (pre : Z -> Prop) z,
        0 <= z < 2 ^ sz ->
        pre z ->
        rep_arg (Leaf_const sz pre) (inr z)
    .

    (* This is all wrong *)
    (* try converting program to graph *)
    Inductive rep : T -> Machine.program -> Prop :=
    | rep_tree_instr :
        forall sz i rd args args',
          length args = length args' ->
          Forall (fun aa => rep_arg (fst aa) (snd aa)) (combine args args') ->
          register_size rd = sz ->
          rep (Tree sz i args) (Machine.Instr i rd args' (Ret rd))
    .
    
                                                                  

    Fixpoint fill_leaves (t : T) (reg_values : list register) (const_values : list const) : program :=
      match t with
      | Leaf_reg _ _ =>
        match reg_values with
          | 

    Fixpoint leaves_t (t : T) : Type :=
      match t with
      | Leaf_reg _ _ => register
      | Leaf_const _ _ => Z
      | Tree _ i args =>
        match args with
        | [] => False
        | a :: args' =>
          fold_right (fun a' out => 
      end.
    
      

    Definition eval
               (t : T)
               (args : 
    

    Require Import Optimizer.ProofOfConcept.Instructions.
    Print precondition.
          