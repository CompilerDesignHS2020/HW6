(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)
let insn_flow ((u,i):uid * insn) (d:fact) : fact =
  
  match i with
    | Alloca(t) -> UidM.add u SymPtr.Unique d
    | Load(t, op) -> 
      begin match t with
        | Ptr(Ptr(inner)) -> UidM.add u SymPtr.MayAlias d
        | _ -> d
      end
    | Bitcast(in_ty, in_id, out_ty) -> 
      let temp_uid_map = 
      begin match in_ty, in_id with
        Ptr(inner_in_ty), Ll.Id(in_uid) -> UidM.add in_uid (SymPtr.MayAlias) d 
        | _ -> d
      end in
      begin match out_ty with
        Ptr(inner_out_ty) -> UidM.add u SymPtr.MayAlias temp_uid_map
        | _ -> temp_uid_map
      end
    
    | Gep(in_ty, in_id, out_ty) -> 
      let temp_uid_map =  
      match in_id with 
        | Ll.Id(in_uid) -> UidM.add in_uid (SymPtr.MayAlias) d 
        | _ -> d
      in
      UidM.add u SymPtr.MayAlias temp_uid_map

    | Store(ty, Ll.Id(src_uid), dest_op) -> 
      begin match ty with
        | Ptr(inner) -> UidM.add src_uid (SymPtr.MayAlias) d 
        | _ -> d
      end

    | Call(ret_ty, fun_lbl, arg_list) -> 
      let rec update_map rem_args act_map =
        begin match rem_args with
          | (act_ty, Ll.Id(act_uid))::tl -> 
            begin match act_ty with
              | Ptr(inner) -> update_map tl (UidM.add act_uid SymPtr.MayAlias act_map)
              | _ -> update_map tl act_map
            end
          | (act_ty, _)::tl ->  update_map tl act_map
          | [] -> act_map
        end
      in
      let temp_map = update_map arg_list d in 
      begin match ret_ty with
        | Ptr(inner) -> UidM.add u SymPtr.MayAlias temp_map
        | _ -> temp_map
      end

    | _ -> d
    
    

(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)
    
    let merge_sym_ptr uid val_1 val_2 =
      begin match val_1, val_2 with
        | None, None -> None
        | None, Some x -> Some x
        | Some x, None -> Some x
        | Some SymPtr.MayAlias, _ -> Some SymPtr.MayAlias
        | _, Some SymPtr.MayAlias -> Some SymPtr.MayAlias
        | Some SymPtr.UndefAlias, Some x -> Some x
        | Some x, Some SymPtr.UndefAlias -> Some x
        | Some SymPtr.Unique, Some SymPtr.Unique -> Some SymPtr.Unique
      end

    let combine (ds:fact list) : fact =

      let rec join_rem_facts rem_facts=
        begin match rem_facts with
          | h::tl -> UidM.merge merge_sym_ptr h (join_rem_facts tl)
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
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

