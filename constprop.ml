open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
let insn_flow (u,i:uid * insn) (d:fact) : fact =
  
  let calc_icmp_res (cond:cnd) (val1: int) (val2: int) : int64 =
    1L (* TODO *)
  in

  let calc_binop_res (binop:Ll.bop) (val1) (val2) =
    begin match binop with
      | Add -> Int64.of_int (val1 + val2)
      | Sub -> Int64.of_int (val1 - val2)
      | Mul -> Int64.of_int (val1 * val2)
      | Shl -> Int64.of_int (val1 lsl val2)
      | Lshr -> Int64.of_int (val1 lsr val2)
      | Ashr -> Int64.of_int (val1 asr val2)
      | And -> Int64.of_int (val1 land val2)
      | Or -> Int64.of_int (val1 lor val2)
      | Xor -> Int64.of_int (val1 lxor val2)
    end
  in

  (* returns is_const, is_defined, const_value *)
  let calculate_op_value op =
    begin match op with
      | Null -> true, true, 0
      | Const(i) -> true, true, Int64.to_int i
      | Id(op1_uid) -> 
        let op1_const_ty = UidM.find op1_uid d in
        begin match op1_const_ty with
          | Const i -> true, true, Int64.to_int i
          | NonConst -> false, true, 0
          | UndefConst -> false, false, 0
        end
      | Gid(_) -> false, true, 0
    end
  in


  match i with
  | Binop(bin,_, op1, op2) -> 
    let op1_is_const, op1_is_defined, op1_value = calculate_op_value op1 in
    let op2_is_const, op2_is_defined, op2_value = calculate_op_value op2 in
    begin if (op1_is_const && op2_is_const) then
      UidM.add u (SymConst.Const(calc_binop_res bin op1_value op2_value)) d
    else
      begin if op1_is_defined && op2_is_defined then
        UidM.add u SymConst.NonConst d
      else
        UidM.add u SymConst.UndefConst d
      end
    end

  | Icmp(cond, _, op1, op2) ->
    let op1_is_const, op1_is_defined, op1_value = calculate_op_value op1 in
    let op2_is_const, op2_is_defined, op2_value = calculate_op_value op2 in
    if (op1_is_const && op2_is_const) then
      UidM.add u (SymConst.Const(calc_icmp_res cond op1_value op2_value)) d
    else
      begin if op1_is_defined && op2_is_defined then
        UidM.add u SymConst.NonConst d
      else
        UidM.add u SymConst.UndefConst d
      end

    
  | _ -> d

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
    let combine (ds:fact list) : fact = 
      failwith "Constprop.Fact.combine unimplemented"
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    failwith "Constprop.cp_block unimplemented"
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
