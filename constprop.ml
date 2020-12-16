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

  let print_map_entry = fun uid value -> uid^": "^(SymConst.to_string value) in
  (* print_endline ("At uid :%"^u^" "^(UidM.to_string print_map_entry d)); *)
  
  let calc_icmp_res (cond:cnd) (val1: int64) (val2: int64) : int64 =
    begin match cond with
      | Eq -> Int64.of_int (Bool.to_int (val1 = val2))
      | Ne -> Int64.of_int (Bool.to_int (val1 != val2))
      | Sle -> Int64.of_int (Bool.to_int (val1 <= val2))
      | Slt -> Int64.of_int (Bool.to_int (val1 < val2))
      | Sge -> Int64.of_int (Bool.to_int (val1 >= val2))
      | Sgt -> Int64.of_int (Bool.to_int (val1 > val2))
    end
  in

  let calc_binop_res (binop:Ll.bop) (val1) (val2) =
    begin match binop with
      | Add -> Int64.add val1 val2
      | Sub -> Int64.sub val1 val2
      | Mul -> Int64.mul val1 val2
      | Shl -> Int64.shift_left val1 (Int64.to_int val2)
      | Lshr -> Int64.shift_right_logical val1 (Int64.to_int val2)
      | Ashr -> Int64.shift_right val1 (Int64.to_int val2)
      | And -> Int64.logand val1 val2
      | Or -> Int64.logor val1 val2
      | Xor -> Int64.logxor val1 val2
    end
  in

  (* returns is_const, is_defined, const_value *)
  let calculate_op_value op =
    begin match op with
      | Null -> true, true, 0L
      | Const(i) -> true, true, i
      | Id(op_uid) -> 
        let op_const_ty = UidM.find_opt op_uid d in
        begin match op_const_ty with
          | Some Const i -> true, true, i
          | Some NonConst -> false, true, 0L
          | Some UndefConst -> false, false, 0L
          | None -> false, false, 0L (* failwith ("uid %"^op_uid^" not found") *)
        end
      | Gid(_) -> false, true, 0L
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

  | Store(_,_,_) -> (*UidM.add u SymConst.UndefConst*) d
  | Call(Void,_,_) -> UidM.add u SymConst.UndefConst d
  | _ -> UidM.add u SymConst.NonConst d

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

    let merge_const_types uid val1 val2 =
      match val1, val2 with
        | None, None -> None
        | None, Some x -> Some x
        | Some x, None -> Some x
        | Some SymConst.Const(i1), Some SymConst.Const(i2) -> if i1 = i2 then Some (SymConst.Const(i1)) else Some SymConst.UndefConst
        | Some UndefConst, Some _ -> Some SymConst.UndefConst
        | Some _, Some UndefConst -> Some SymConst.UndefConst
        | Some SymConst.NonConst, Some _ ->  Some SymConst.NonConst
        | Some _, Some SymConst.NonConst ->  Some SymConst.NonConst

    let combine (ds:fact list) : fact = 
      let rec join_rem_facts rem_facts=
      begin match rem_facts with
        | h::tl -> UidM.merge merge_const_types h (join_rem_facts tl)
        | [] -> UidM.empty
      end
      in
      join_rem_facts ds
    

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
