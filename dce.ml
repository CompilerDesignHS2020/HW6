(** Dead Code Elimination  *)
open Ll
open Datastructures


(* expose a top-level analysis operation ------------------------------------ *)
(* TASK: This function should optimize a block by removing dead instructions
   - lb: a function from uids to the live-OUT set at the 
     corresponding program point
   - ab: the alias map flowing IN to each program point in the block
   - b: the current ll block

   Note: 
     Call instructions are never considered to be dead (they might produce
     side effects)

     Store instructions are not dead if the pointer written to is live _or_
     the pointer written to may be aliased.

     Other instructions are dead if the value they compute is not live.

   Hint: Consider using List.filter
 *)
let dce_block (lb:uid -> Liveness.Fact.t) 
              (ab:uid -> Alias.fact)
              (b:Ll.block) : Ll.block =

  let rec block_loop (rem_insns: (string * insn) list) : (string * insn) list =
    begin match rem_insns with
      | (uid, insn)::tl -> 
        begin match insn with
          | Call(a,b,c) -> (block_loop tl)@[uid, Call(a,b,c)]
          | Store(ty,src,dest) -> 
            begin match dest with
              | Ll.Id(uid) -> 
                (* check if dest_uid is live *)
                let liveness = lb uid in 
                let contains_uid = UidS.find_opt uid liveness in
                begin match contains_uid with
                  | None -> 
                    (* check if aliased *)
                    let aliasness = ab uid in
                    let alias_state =  UidM.find uid aliasness in
                    if alias_state = MayAlias then
                      (block_loop tl)@[uid, Store(ty,src,dest)] (* keep instruction *)
                    else
                      block_loop tl (* discard instruction *)
                  | Some x -> (block_loop tl)@[uid, Store(ty,src,dest)] (* keep instruction *)
                end
              | _ -> (block_loop tl)@[uid, Store(ty,src,dest)] (* keep instruction *)
            end

          | other_insn -> 
            let liveness = lb uid in 
            let contains_uid = UidS.find_opt uid liveness in
            match contains_uid with
              | None -> (block_loop tl)
              |  Some x -> (block_loop tl)@[uid, other_insn]
        end
      | [] -> []
    end
  in 
  {insns = block_loop b.insns; term = b.term}



let run (lg:Liveness.Graph.t) (ag:Alias.Graph.t) (cfg:Cfg.t) : Cfg.t =

  LblS.fold (fun l cfg ->
    let b = Cfg.block cfg l in

    (* compute liveness at each program point for the block *)
    let lb = Liveness.Graph.uid_out lg l in

    (* compute aliases at each program point for the block *)
    let ab = Alias.Graph.uid_in ag l in 

    (* compute optimized block *)
    let b' = dce_block lb ab b in
    Cfg.add_block l b' cfg
  ) (Cfg.nodes cfg) cfg

