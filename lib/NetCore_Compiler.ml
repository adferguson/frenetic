open List
open Packet
open NetCore_Types
open NetCore_Pattern
module OF = OpenFlow0x01_Core

module GroupClassifier = NetCore_Classifier.Make(NetCore_Action.Group)

module type POLICYCOMPILER = 
sig
  module OutputClassifier : NetCore_Classifier.CLASSIFIER
  module BoolClassifier : NetCore_Classifier.CLASSIFIER 

  (* val flow_table_of_policy :  *)
  (*   OpenFlow0x01.switchId  *)
  (*   -> NetCore_Types.pol  *)
  (*   -> (OpenFlow0x01.Match.t * OpenFlow0x01.Action.sequence) list *)

  (* val query_fields_of_policy :  *)
  (*   NetCore_Types.pol  *)
  (*   -> NetCore_Types.action_atom *)
  (*   -> OpenFlow0x01.switchId *)
  (*   -> OpenFlow0x01.Match.t list *)

  val compile_pol : 
    NetCore_Types.pol 
    -> OpenFlow0x01.switchId 
    -> OutputClassifier.t

  val compile_pred :
    NetCore_Types.pred
    -> OpenFlow0x01.switchId
    -> BoolClassifier.t
end

module type MAKE = functor (Output : NetCore_Action.COMPILER_ACTION0x01) ->
sig include POLICYCOMPILER end
  with type OutputClassifier.action = Output.t
  and type BoolClassifier.action = bool

module CompilePol (Output : NetCore_Action.COMPILER_ACTION0x01) = struct

  module OutputClassifier = NetCore_Classifier.Make(Output)
  module BoolClassifier = NetCore_Classifier.Make(NetCore_Action.Bool)

  let rec compile_pred pr sw : BoolClassifier.t = 
    match pr with
    | Hdr pat -> 
      [(pat,NetCore_Action.Bool.pass,[]); (all, NetCore_Action.Bool.drop,[])]
    | OnSwitch sw' ->
      if sw = sw' then
        [(all, NetCore_Action.Bool.pass, [])]
      else 
        [(all, NetCore_Action.Bool.drop, [])]
    | Or (pr1, pr2) ->
      BoolClassifier.union (compile_pred pr1 sw) (compile_pred pr2 sw)
    | And (pr1, pr2) ->
      BoolClassifier.sequence (compile_pred pr1 sw) (compile_pred pr2 sw)
    | Not pr' ->    
      map (fun (a,b,meta) -> (a, not b, meta))
        (compile_pred pr' sw @ [(all,NetCore_Action.Bool.drop,[])])
    | Everything -> 
      [all,NetCore_Action.Bool.pass,[]]
    | Nothing -> 
      [all,NetCore_Action.Bool.drop,[]]

  let rec compile_pol p sw =
    let compile_action action meta =
      fold_right 
        (fun e0 tbl -> 
           OutputClassifier.union 
             [(Output.domain e0, Output.to_action e0, meta)]
             tbl)
        (Output.atoms (Output.from_nc_action action))
        [(all, Output.drop, [])] in
    match p with
    | HandleSwitchEvent _ -> [(all, Output.drop, [])]
    | Action action -> compile_action action []
    | ActionChoice _ -> failwith "NYI compile_pol ActionChoice"
    | ActionWithMeta (action, meta) -> compile_action action meta
    | Filter pred -> 
      map 
	(fun (a,b,meta) -> match b with
	  | true -> (a, Output.pass, meta)
	  | false -> (a, Output.drop, meta))
	(compile_pred pred sw)
    | Union (pol1, pol2) ->
      OutputClassifier.union 
        (compile_pol pol1 sw) 
        (compile_pol pol2 sw)
    | Seq (pol1, pol2) ->
      OutputClassifier.sequence 
        (compile_pol pol1 sw) 
        (compile_pol pol2 sw)
    | ITE (pred, then_pol, else_pol) ->
      let then_tbl = compile_pol then_pol sw in
      let else_tbl = compile_pol else_pol sw in
      let seq_then_else (pat, b, meta) = match b with
	| true ->
          OutputClassifier.sequence
            [(pat, Output.pass, meta)] then_tbl
	| false ->
          OutputClassifier.sequence
            [(pat, Output.pass, meta)] else_tbl in
      Frenetic_List.concat_map seq_then_else (compile_pred pred sw)
    | Choice _ -> 
      failwith "compile_pol: not yet implemented"

end

module NetCoreGroupCompiler = struct

  module Output = NetCore_Action.Group

  module OutputClassifier = NetCore_Classifier.Make(Output)
  module BoolClassifier = NetCore_Classifier.Make(NetCore_Action.Bool)

  (* JNF: we're copying a lot of code here... ;-/ *)
	    
  let rec compile_pred pr sw : BoolClassifier.t= 
    match pr with
      | Hdr pat -> 
	[(pat,NetCore_Action.Bool.pass,[]); (all, NetCore_Action.Bool.drop,[])]
      | OnSwitch sw' ->
        if sw = sw' then
          [(all, NetCore_Action.Bool.pass, [])]
        else 
          [(all, NetCore_Action.Bool.drop, [])]
      | Or (pr1, pr2) ->
        BoolClassifier.union (compile_pred pr1 sw) (compile_pred pr2 sw)
      | And (pr1, pr2) ->
        BoolClassifier.sequence (compile_pred pr1 sw) (compile_pred pr2 sw)
      | Not pr' ->    
        map (fun (a,b,meta) -> (a, not b, meta))
          (compile_pred pr' sw @ [(all,NetCore_Action.Bool.drop,[])])
      | Everything -> 
        [all,NetCore_Action.Bool.pass,[]]
      | Nothing -> 
        [all,NetCore_Action.Bool.drop,[]]

  let rec compile_pol p sw =
    let compile_action action meta =
        fold_right 
          (fun e0 tbl -> 
            OutputClassifier.union 
              [(Output.domain e0, Output.to_action e0, meta)]
              tbl)
          (Output.atoms (Output.from_nc_action action))
          [(all, Output.drop, [])] in
    match p with
      | HandleSwitchEvent _ -> [(all, Output.drop, [])]
      | Action action -> compile_action action []
      | ActionChoice _ -> failwith "NYI compile_pol ActionChoice"
      | ActionWithMeta (action, meta) -> compile_action action meta
      | Filter pred -> 
	map 
	  (fun (a,b,meta) -> match b with
	    | true -> (a, Output.pass, meta)
	    | false -> (a, Output.drop, meta))
	  (compile_pred pred sw)
      | Union (pol1, pol2) ->
        OutputClassifier.union 
          (compile_pol pol1 sw) 
          (compile_pol pol2 sw)
      | Seq (pol1, pol2) ->
        OutputClassifier.sequence 
          (compile_pol pol1 sw) 
          (compile_pol pol2 sw)
      | ITE (pred, then_pol, else_pol) ->
	let then_tbl = compile_pol then_pol sw in
	let else_tbl = compile_pol else_pol sw in
	let seq_then_else (pat, b, meta) = match b with
	  | true ->
            OutputClassifier.sequence
              [(pat, Output.pass, meta)] then_tbl
	  | false ->
            OutputClassifier.sequence
              [(pat, Output.pass, meta)] else_tbl in
	Frenetic_List.concat_map seq_then_else (compile_pred pred sw)
      | Choice (pol1, pol2) ->
        OutputClassifier.choice
          (compile_pol pol1 sw) 
          (compile_pol pol2 sw)

end

module NetCoreCompiler = CompilePol(NetCore_Action.Output)
