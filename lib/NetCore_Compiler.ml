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

  let rec compile_pol_helper p sw =
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
    | Action action ->
              (*Printf.printf "compile_action for: %s\n%!" (NetCore_Pretty.string_of_action action);*)
      compile_action action []
    | ActionChoice _ -> failwith "NYI compile_pol_helper ActionChoice"
    | ActionWithMeta (action, meta) -> compile_action action meta
    | Filter pred ->
      map
	(fun (a,b,meta) -> match b with
	  | true -> (a, Output.pass, meta)
	  | false -> (a, Output.drop, meta))
	(compile_pred pred sw)
    | Union (pol1, pol2) ->
      OutputClassifier.union
        (compile_pol_helper pol1 sw)
        (compile_pol_helper pol2 sw)
    | Seq (pol1, pol2) ->
      OutputClassifier.sequence
        (compile_pol_helper pol1 sw)
        (compile_pol_helper pol2 sw)
    | ITE (pred, then_pol, else_pol) ->
      let then_tbl = compile_pol_helper then_pol sw in
      let else_tbl = compile_pol_helper else_pol sw in
      let seq_then_else (pat, b, meta) = match b with
	| true ->
          OutputClassifier.sequence
            [(pat, Output.pass, meta)] then_tbl
	| false ->
          OutputClassifier.sequence
            [(pat, Output.pass, meta)] else_tbl in
      Frenetic_List.concat_map seq_then_else (compile_pred pred sw)
    | Choice _ ->
      failwith "compile_pol_helper: not yet implemented";;

  (* OutputClassifier.t is: (NetCore_Types.ptrn * [Output.t] action * NetCore_Types.ruleMeta) list *)
  (* Detect situations where there is no in_port constraint in the predicate, yet there is a concrete output port in the action.
     We need to split the rule in two in this case, or we will fail to use the IN_PORT action for traffic whose port is unchanged. *)
  let make_inport_rule ptrn act rmeta inport =
    let new_ptrn = {ptrn with ptrnInPort = NetCore_Wildcard.WildcardExact(inport)} in
    (* maintain ordering of action atoms when substituting *)
    let new_act = Output.from_nc_action (fold_right
           (fun atom acc -> match atom with
              | SwitchAction(x) when x.outPort = inport -> SwitchAction({x with outPort=Here})::acc
              | _ ->atom::acc)
         (Output.atoms act) []) in (* maintain action atom ordering*)
    (new_ptrn, new_act, rmeta);;

  let compile_pol p sw  =
    (* may contain rules without a port in pred, but concrete ports in output. need to use in_port action. *)
    let unsafe_table = compile_pol_helper p sw in

(*
  let pam_printer = fun (p, a, m) -> Printf.printf "%s -> %s  $  Meta: %s\n%!"
                                                   (NetCore_Pretty.string_of_pattern p)
                                                   (NetCore_Pretty.string_of_action (Output.atoms a))
                                                   (NetCore_Pretty.string_of_ruleMeta m) in


    Printf.printf "\n\nINPORT_FILTERED_COMPILE: Switch: %Ld.\n%!" sw;
    ignore (List.map pam_printer unsafe_table);*)


      (* fold_right to maintain ordering *)
      fold_right (fun (ptrn,act,rmeta) acc ->

    (* debug*)
    (*
        let sas = List.filter (fun atom -> match atom with | SwitchAction(out) -> true | _ -> false) (Output.atoms act) in
        List.iter (fun swact -> match swact with SwitchAction(out) ->
            if (out.outDlSrc <> None && out.outDlSrc = out.outDlDst) then
              Printf.printf "debug in safety EQUAL DL MODS for: %s\n%!" (Output.string_of_action act)) sas;
*)

          match ptrn.ptrnInPort with
            | NetCore_Wildcard.WildcardAll ->
              (* Dangerous rule. I.e., no port constraint in pred.
                 Caveat: if this code is called more than once, we'll get identical added rules. *)

              let (outports_in_action: NetCore_Types.port list) =
                (* "All" action is safe (implicit no backflood). Including ALL here leads to confusing bugs,
                   as a rule like dlTyp=0x1001 --> all becomes
                   dlTyp=0x1001 & inport=any --> here (which leads to loops) *)
                fold_left (fun acc2 atom -> match atom with
                    | SwitchAction(outp) ->
                      (match outp.outPort with
                          | Physical(_) -> outp.outPort::acc2
                          | _ -> acc2)
                    | _ -> acc2) [] (Output.atoms act) in

              let new_rules = fold_right (fun inport acc2 -> (make_inport_rule ptrn act rmeta inport)::acc2) outports_in_action [] in

              (*
              Printf.printf "(%Ld) Current rule:\n%!" sw;
              pam_printer (ptrn,act,rmeta);
              Printf.printf "(%Ld) Size of outports_in_action: %d. NC act: %s. Output act: %s.\n%!" sw (List.length outports_in_action)
                (NetCore_Pretty.string_of_action (Output.atoms act))
                (Output.string_of_action act);

              (* keep original rule, but precede by specific checks for every port used in action *)
              let result = (new_rules@[(ptrn,act,rmeta)])@acc in
              Printf.printf "(%Ld) Full new list:\n%!" sw;
              iter pam_printer result; (* could something be happening afterward? optimization gone wrong? A: no. before. *)
              result *)
              (new_rules@[(ptrn,act,rmeta)])@acc
            | _ ->
              (* predicate has constraint on in_port; keep the rule by itself *)
              (ptrn,act,rmeta)::acc)
        (* fold over every rule *)
        unsafe_table [];;


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
