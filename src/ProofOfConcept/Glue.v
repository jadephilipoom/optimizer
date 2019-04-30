Require Import Coq.ZArith.ZArith.
Require Import Optimizer.Machine.
Require Import Optimizer.System.
Require Import Optimizer.ProofOfConcept.CostModel.
Require Import Optimizer.ProofOfConcept.Flags.
Require Import Optimizer.ProofOfConcept.Optimality.
Require Import Optimizer.ProofOfConcept.Maps.
Require Import Optimizer.ProofOfConcept.Registers.
Require Optimizer.ProofOfConcept.Instructions.
Local Open Scope Z_scope.

Instance regt : reg_impl :=
  {|
    register := Registers.register;
    reg_mapt := Maps.RegMaps.reg_mapt;
    reg_enum := {|
                 enum := Registers.all_registers;
                 enum_complete := all_registers_complete;
               |};
    register_size := Registers.size;
    reg_eq_dec := Registers.reg_eq_dec
  |}.
Instance flagt : flag_impl :=
  {|
    flag := Flags.flag;
    flag_mapt := Maps.FlagMaps.flag_mapt;
    flag_enum := {|
                  enum := Flags.all_flags;
                  enum_complete := all_flags_complete
                |};
    flag_spec := Flags.flag_spec;
    flag_eq_dec := Flags.flag_eq_dec;
  |}.
Instance instrt : instr_impl :=
  {|
    instruction := Instructions.instruction;
    instr_enum := {|
                   enum := Instructions.all_instructions;
                   enum_complete := Instructions.all_instructions_complete;
                 |};
    flags_written := Instructions.flags_written;
    flags_read := Instructions.flags_read;
    num_source_regs := Instructions.num_source_regs;
    spec := Instructions.spec;
    precondition := Instructions.precondition (register_size:=Registers.size);
    flags_read_correct := Instructions.flags_read_correct;
    instr_eq_dec := Instructions.instr_eq_dec;
    precondition_dec := Instructions.precondition_dec;
  |}.

Notation cost := (CostModel.cost
                    (instr_cost:=Instructions.instr_cost)).
Notation optimal := (Optimality.optimal cost).
Lemma instr_cost_eq i rd args cont :
  cost (Machine.Instr i rd args cont) = (cost cont + Instructions.instr_cost i)%nat.
Proof. cbn [CostModel.cost]. omega. Qed.
Lemma ret_cost_eq r : cost (Machine.Ret r) = 0%nat.
Proof. reflexivity. Qed.
Notation optimal_limited_domain_equiv :=
  (Optimality.optimal_limited_domain_equiv
     cost
     (CostModel.cost_of_instr_pos Instructions.instr_cost_pos)
     (Enumerators.enumerate_programs_under_cost Instructions.instr_cost Instructions.instr_size)
     (Enumerators.enumerate_under_cost_with_condition Instructions.instr_cost Instructions.instr_size)
     (Enumerators.enumerate_programs_under_cost_complete_alt
        Instructions.instr_cost
        Instructions.instr_size
        cost
        Instructions.instr_cost_pos
        instr_cost_eq
        Instructions.precondition_instr_size
        Instructions.precondition_length_args)
     (Enumerators.enumerate_under_cost_with_condition_complete
        Instructions.instr_cost
        Instructions.instr_size
        cost
        Instructions.instr_cost_pos
        instr_cost_eq
        Instructions.precondition_instr_size
        Instructions.precondition_length_args)
     (Enumerators.enumerate_under_cost_with_condition_sound
        Instructions.instr_cost
        Instructions.instr_size)
     (Enumerators.enumerate_under_cost_with_condition_bound
        Instructions.instr_cost
        Instructions.instr_size
        cost
        Instructions.instr_cost_pos
        ret_cost_eq
        instr_cost_eq
     )
     (Enumerators.enumerate_under_cost_with_condition_zero
        Instructions.instr_cost
        Instructions.instr_size)
     Enumerators.enumerate_contexts
     (Enumerators.enumerate_contexts_complete Maps.reg_map_equiv)
     Maps.flag_map_equiv
     (fun m1 m2 => Maps.reg_map_dec m1 m2 Z.eq_dec)
     (fun m1 m2 => Maps.flag_map_dec m1 m2 Bool.bool_dec)
  ).