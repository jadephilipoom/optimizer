Require Import Coq.ZArith.ZArith.
Require Import Optimizer.Machine.
Require Import Optimizer.ProofOfConcept.CostModel.
Require Import Optimizer.ProofOfConcept.Flags.
Require Import Optimizer.ProofOfConcept.Instructions.
Require Import Optimizer.ProofOfConcept.Optimality.
Require Import Optimizer.ProofOfConcept.Maps.
Require Import Optimizer.ProofOfConcept.Registers.
Local Open Scope Z_scope.
Import Maps.

Notation exec := (Machine.exec
                    (register_size:=Registers.size)
                    (flag_spec:=Flags.flag_spec)
                    (flags_written:=Instructions.flags_written)
                    (spec:=Instructions.spec)).
Notation precondition :=
  (Instructions.precondition (register_size:=Registers.size)).
Notation valid := (Machine.valid
                     (register:=Registers.register)
                     (precondition:=precondition)).
Notation program := (Machine.program
                       (register:=Registers.register)
                       (instruction:=Instructions.instruction)).
Notation valid_context := (Machine.valid_context
                             (register:=Registers.register)
                             (register_size:=Registers.size)).
Notation equivalent := (Machine.equivalent
                          (register_size:=Registers.size)
                          (flag_spec := Flags.flag_spec)
                          (flags_written := Instructions.flags_written)
                          (spec := Instructions.spec)).
Infix "==" := equivalent (at level 40).
Notation cost := (CostModel.cost
                    (register:=Registers.register)
                    (instr_cost:=Instructions.instr_cost)).
Notation optimal := (CostModel.optimal
                       (instr_cost:=Instructions.instr_cost)
                       (precondition:=precondition)
                       equivalent).

(* TODO: make this rely on fewer things (for instance, parameterize over [equivalent]) *)
Notation optimal_limited_domain_equiv :=
  (Optimality.optimal_limited_domain_equiv
     reg_map_equiv
     flag_map_equiv
     Instructions.instr_size
     Registers.size
     Instructions.instr_cost
     Instructions.num_source_regs
     precondition
     Flags.flag_spec
     Instructions.flags_written
     Instructions.spec
     Flags.flag_eq_dec
     Registers.reg_eq_dec
     Instructions.instr_eq_dec
     (fun m1 m2 => reg_map_dec m1 m2 Z.eq_dec)
     (fun m1 m2 => flag_map_dec m1 m2 Bool.bool_dec)
     Flags.all_flags
     Registers.all_registers
     Instructions.all_instructions
     all_flags_complete
     all_registers_complete
     all_instructions_complete
     instr_cost_pos
     precondition_instr_size
     precondition_length_args
     precondition_dec
  ).