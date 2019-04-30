Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Optimizer.AbstractMap.

Class enumerator T :=
  {
    enum : list T;
    enum_complete : forall t : T, In t enum;
  }.
Hint Resolve @enum_complete.

Class reg_impl :=
  {
    register : Type;
    reg_mapt : map_impl register;
    reg_enum : enumerator register;
    register_size : register -> Z;
    reg_eq_dec : forall r1 r2 : register, {r1 = r2} + {r1 <> r2};
  }.

Class flag_impl :=
  {
    flag : Type;
    flag_mapt : map_impl flag;
    flag_enum : enumerator flag;
    flag_spec : Z (* destination register size *) -> flag -> Z -> bool;
    flag_eq_dec : forall f1 f2 : flag, {f1 = f2} + {f1 <> f2};
  }.

Class instr_impl {regt : reg_impl} {flagt : flag_impl} :=
  {
    instruction : Type;
    instr_enum : enumerator instruction;
    flags_read : instruction -> list (@flag flagt);
    flags_written : instruction -> list (@flag flagt);
    num_source_regs : instruction -> nat;
    spec : instruction -> list Z -> (@flag flagt -> bool) -> Z;
    precondition : instruction -> @register regt -> list (@register regt + Z) -> Prop;
    flags_read_correct :
      forall i f,
        ~ (In f i.(flags_written)) ->
        forall v args flag_values,
          spec i args (get (map_impl:=flag_mapt) (update flag_values f v)) =
          spec i args (get (flag_values));
    instr_eq_dec : forall i1 i2 : instruction, {i1 = i2} + {i1 <> i2};
    precondition_dec : forall i rd args, {precondition i rd args} + {~ precondition i rd args};
  }.

(*
(* TODO: not currently in use because maps are not abstract state yet *)
Class machine_impl :=
  {
    state : Type;
    program : Type;
    valid : program -> Prop;
    valid_state : state -> Prop;
    exec : program -> state -> state;
    equivalent : program -> program -> Prop;
    valid_dec : forall p, {valid p} + {~ valid p};
    equiv_dec : forall p1 p2, {equivalent p1 p2} + {~ equivalent p1 p2};
    program_eq_dec : forall p1 p2 : program, {p1 = p2} + {p1 <> p2};
    (*
    (* TODO: this seems like maybe a natural property to want *)
    exec_preserves_valid :
      forall s p, valid_state s -> valid p -> valid_state (exec p s)
     *)
  }.
*)