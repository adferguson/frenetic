open NetCore_Wildcard
module P = NetCore_Pattern

module Compat0x01 =
struct
  open OpenFlow0x01
  open OpenFlow0x01_Core
  open NetCore_Types
  module NetCoreCompiler = NetCore_Compiler.NetCoreCompiler

  module PrioritizedFlow = struct

    type t =
      { prio : Packet.int16
      ; pattern : OpenFlow0x01_Core.pattern (* = OpenFlow0x01.Match.t *)
      ; actions : OpenFlow0x01_Core.action list
      ; idle_to : OpenFlow0x01_Core.timeout (* does not affect comparison *)
      }

    let compare x y =
      let prio_cmp = Pervasives.compare x.prio y.prio in
      if prio_cmp != 0 then
        prio_cmp
      else
        let pattern_cmp = Pervasives.compare x.pattern y.pattern in
        if pattern_cmp != 0 then
          pattern_cmp
        else
          Pervasives.compare x.actions y.actions

  end

  module PrioritizedFlowTable = Set.Make (PrioritizedFlow)

  let to_of_portId = Int32.to_int
  let to_nc_portId = Int32.of_int

  let to_nc_caps caps =
    { flow_stats = caps.SwitchFeatures.Capabilities.flow_stats;
      table_stats = caps.SwitchFeatures.Capabilities.table_stats;
      port_stats = caps.SwitchFeatures.Capabilities.port_stats;
      group_stats = false;
      ip_reasm = caps.SwitchFeatures.Capabilities.ip_reasm;
      queue_stats = caps.SwitchFeatures.Capabilities.queue_stats;
      port_blocked = false
    }

  let to_nc_features feat =
    { datapath_id = feat.SwitchFeatures.switch_id;
      num_buffers = Int32.to_int feat.SwitchFeatures.num_buffers;
      num_tables = feat.SwitchFeatures.num_tables;
      supported_capabilities = to_nc_caps feat.SwitchFeatures.supported_capabilities;
      ports = List.map (fun x -> to_nc_portId x.PortDescription.port_no) feat.SwitchFeatures.ports
    }

  let set upd mk lst = match upd with
    | Some (_,nw) ->
      (mk nw) :: lst
    | None ->
      lst

  let unset upd mk lst = match upd with
    | Some (Some(od),_) ->
      (mk od) :: lst
    | Some (None,_) ->
      lst
    | None ->
      lst

  let modify out =
    set out.outDlSrc (fun x -> SetDlSrc x)
      (set out.outDlDst (fun x -> SetDlDst x)
         (set out.outDlVlan (fun x -> SetDlVlan x)
            (set out.outDlVlanPcp (fun x -> SetDlVlanPcp x)
               (set out.outNwSrc (fun x -> SetNwSrc x)
                  (set out.outNwDst (fun x -> SetNwDst x)
                     (set out.outNwTos (fun x -> SetNwTos x)
                        (set out.outTpSrc (fun x -> SetTpSrc x)
                           (set out.outTpDst (fun x -> SetTpDst x) []))))))))

  let unmodify out =
    unset out.outDlSrc (fun x -> SetDlSrc x)
      (unset out.outDlDst (fun x -> SetDlDst x)
         (unset out.outDlVlan (fun x -> SetDlVlan x)
            (unset out.outDlVlanPcp (fun x -> SetDlVlanPcp x)
               (unset out.outNwSrc (fun x -> SetNwSrc x)
                  (unset out.outNwDst (fun x -> SetNwDst x)
                     (unset out.outNwTos (fun x -> SetNwTos x)
                        (unset out.outTpSrc (fun x -> SetTpSrc x)
                           (unset out.outTpDst (fun x -> SetTpDst x) []))))))))

  let nc_port_to_of p = match p with
    | P.Physical p -> PhysicalPort (to_of_portId p)
    | P.All -> AllPorts
    | P.Here -> InPort
    | _ -> failwith "nc_port_to_of: Don't know how to handle this port type"

  let output_to_of inp out = match out.outPort with
    | P.Here -> [] (* Fishy, IMO. Shouldn't this be InPort? *)
    | P.All -> modify out @ (Output AllPorts)
                            :: unmodify out
    | P.Physical pt ->
      modify out @
        (( match inp with
            | Some pt' when (=) pt' pt ->
              Output InPort
            | _ ->
              Output (PhysicalPort (to_of_portId pt))) ::
           (unmodify out))
    | _ -> failwith "output_to_of: Don't know how to handle this port type"

  let atom_to_of inp atom = match atom with
    | SwitchAction out -> output_to_of inp out
    | ControllerAction _ -> [ Output (Controller 65535) ]
    | ControllerQuery _ -> []
    | LeaveBufferedAction -> []

  let as_actionSequence inp act = 
    let of_atoms = Frenetic_List.concat_map (atom_to_of inp) act in
    let controller_atoms, not_controller_atoms =
      List.partition
        (function | Output (Controller _) -> true | _ -> false)
        of_atoms in
    if List.length controller_atoms > 0 then
      not_controller_atoms @ [List.hd controller_atoms]
    else
      not_controller_atoms

  let get_idle_timeout meta =
    try
      match List.find (function | IdleTimeout _ -> true | _ -> false) meta with
        IdleTimeout ito -> ito
    with Not_found -> OpenFlow0x01_Core.Permanent

  let to_rule (prio, pattern, action, meta) =
    match NetCore_Pattern.to_match0x01 pattern with
    | Some match_ ->
      Some {PrioritizedFlow.prio = prio; pattern = match_;
            idle_to = get_idle_timeout meta;
            actions = as_actionSequence
              (match match_.OpenFlow0x01_Core.inPort with
               | None -> None
               | Some pt -> Some (to_nc_portId pt))
              action}
    | None -> None

  let is_overlapped = fun (p1, _, _) (p2, _, _) ->
                          not (NetCore_Pattern.is_empty (NetCore_Pattern.inter p1 p2));;

  (* Sorts a table to minimize the number of priorites which will be needed
   *
   * Input: A table already topologically-sorted
   * Output: Same table, with order respected, but with transitions grouped
   *
   * We are effectively interested in the BFS-based topological sort, but we will
   * need to do an O(N^2) pass over the flow table to infer all of the dependencies
   *)
  let sorted_table table =

    (* To start, we annotate each rule with its "depth". Depth is defined as:
     * - A rule with no overlapping rules preceeding it in the flow table
     *   is at depth 0.
     * - Otherwise, a rule's depth is 1 + the maximum depth of all rules
     *   preceeding it in the flow table which it intersects/overlaps
     * In other words, depth is the length of the longest sequence of
     * intersecting rules ending at this rule.
     *)

    let overlap_max = fun cur_flow cur_max (depth, flow) ->
      if is_overlapped flow cur_flow then max cur_max depth
      else cur_max in

    let rec compute_depths = function
      | [] -> []
      | flow :: l -> let depths = compute_depths l in
                     let max_depth = List.fold_left (overlap_max flow) (-1) depths in
                     (1 + max_depth, flow) :: depths in

    let depth_table = List.rev (compute_depths (List.rev table)) in

    (* Now that we have determined the maximum "depth" of each rule in the
     * flow table, stably re-sort by depth to minimize the number of priority
     * transitions, and then drop the depth annotations. *)
    let sorted_table = List.stable_sort (fun (d1, _) (d2, _) -> compare d1 d2)
                                        depth_table in
    List.map (fun (depth, f) -> f) sorted_table


  (* Assigns priorities to rules to resolve overlaps. Sequences of
   * non-overlapping rules ("groups" in the code below) will be assigned
   * the same priority.
   *)
  let prioritized_table table =

    let split = fun hd group -> try ignore(List.find (is_overlapped hd) group); true
                                with Not_found -> false in

    let rec merge_priority = (fun group lst ->
                              match lst with
                              | [] -> (group, [])
                              | _  -> let hd = List.hd lst in
                                      if (split hd group)
                                      then (group, lst)
                                      else merge_priority (hd :: group) (List.tl lst)) in

    let rec group_by_priority = (fun lst ->
                                 match merge_priority [] lst with
                                 | ([], []) -> []
                                 | (group, []) -> [group]
                                 | (group, lst') -> group :: (group_by_priority lst')) in

    let groups = group_by_priority table in

    let prio = ref 65536 in
    let prioritized_groups = List.map (fun group -> (decr prio; (!prio, group))) groups in

    let attach_priority = fun prio (pattern, action, meta) -> (prio, pattern, action, meta) in
    List.concat(List.map
                (fun (prio, group) -> List.map (attach_priority prio) group)
                prioritized_groups)


  let pam_printer = fun (p, a, m) -> Printf.printf "%s -> %s  $  Meta: %s\n%!"
                                                   (NetCore_Pretty.string_of_pattern p)
                                                   (NetCore_Pretty.string_of_action a)
                                                   (NetCore_Pretty.string_of_ruleMeta m)

  let flow_table_of_policy sw pol0 =
    let table = sorted_table (NetCoreCompiler.compile_pol pol0 sw) in
    (* ignore (List.map pam_printer table); *)
    List.fold_right
      (fun p acc -> match to_rule p with None -> acc | Some r -> PrioritizedFlowTable.add r acc)
      (prioritized_table table)
      PrioritizedFlowTable.empty
end

module Compat0x04 =
struct
  open OpenFlow0x04
  open OpenFlow0x04_Core
  open NetCore_Types
  module NetCoreCompiler = NetCore_Compiler.NetCoreGroupCompiler

  let to_of_portId x = x
  let to_nc_portId x = x

  let convert_of_caps_to_nc_caps caps = 
    { flow_stats = caps.OpenFlow0x04_Core.flow_stats;
      table_stats = caps.OpenFlow0x04_Core.table_stats;
      port_stats = caps.OpenFlow0x04_Core.port_stats;
      group_stats = caps.OpenFlow0x04_Core.group_stats;
      ip_reasm = caps.OpenFlow0x04_Core.ip_reasm;
      queue_stats = caps.OpenFlow0x04_Core.queue_stats;
      port_blocked = caps.OpenFlow0x04_Core.port_blocked }

  let to_nc_features feat portDescs =
    { datapath_id = feat.SwitchFeatures.datapath_id;
      num_buffers = Int32.to_int feat.SwitchFeatures.num_buffers;
      num_tables = feat.SwitchFeatures.num_tables;
      supported_capabilities = convert_of_caps_to_nc_caps feat.SwitchFeatures.supported_capabilities;
      ports = List.map (fun x -> x.OpenFlow0x04_Core.port_no) portDescs
    }

  let as_actionSequence inp acts = match acts with
    | [] -> []
    | act :: acts -> Compat0x01.as_actionSequence inp act

  let maybe_openflow0x01_modification newVal mkModify =
    match newVal with
    | Some (_,v) -> (mkModify v)::[]
    | None -> []


  (** val modification_to_openflow0x01 : modification -> actionSequence **)

  (* TODO: just omitting most mods (NW_SRC etc) because 1.3 parser is a little behind *)
  let modification_to_openflow0x01 mods =
    let { outDlSrc = dlSrc; outDlDst = dlDst; outDlVlan = dlVlan;
          outDlVlanPcp = dlVlanPcp; outNwSrc = nwSrc; outNwDst = nwDst;
          outNwTos = nwTos; outTpSrc = tpSrc; outTpDst = tpDst } = mods
    in
    (maybe_openflow0x01_modification dlSrc (fun x -> SetField (OxmEthSrc (val_to_mask x)))) 
    @ (maybe_openflow0x01_modification dlDst (fun x -> SetField (OxmEthDst (val_to_mask x))))
    (* If vlan, create vlan tag *)
    @ (match (dlVlan, dlVlanPcp) with
        | (Some (_,None),_) -> [PopVlan]
        | (Some (_,(Some n)),_) -> [PushVlan]
        | (_, _) -> [])
    @ (maybe_openflow0x01_modification dlVlanPcp (fun x -> SetField (OxmVlanPcp x)))
    @ (match dlVlan with
        | Some (_,None) -> []
        | Some (_,(Some n)) -> [SetField (OxmVlanVId (val_to_mask n))]
        | None -> [])

  (** val translate_action : portId option -> act -> actionSequence **)

  module OF10 = OpenFlow0x01_Core

  let translate_action in_port = function
    | OF10.Output p ->
      (match p with
       | OF10.PhysicalPort pp ->
         let pp = Int32.of_int pp in
         (match in_port with
          | Some pp' ->
            if pp' = pp
            then
              [Output InPort]
            else
              [Output (PhysicalPort pp)]
          | None -> [Output (PhysicalPort pp)])
       | OF10.InPort -> [Output InPort]
       | OF10.AllPorts -> [Output AllPorts]
       | OF10.Controller x -> [Output (Controller x)]
       | OF10.Flood -> [Output Flood])
    | OF10.SetDlVlan (Some vlan) -> [PushVlan; SetField (OxmVlanVId (val_to_mask vlan))]
    | OF10.SetDlVlan None -> [PopVlan]
    | OF10.SetDlVlanPcp vpcp -> [SetField (OxmVlanPcp vpcp)]
    | OF10.SetDlSrc src -> [SetField (OxmEthSrc (val_to_mask src))]
    | OF10.SetDlDst dst -> [SetField (OxmEthDst (val_to_mask dst))]
    | OF10.SetNwSrc src -> [SetField (OxmIP4Src (val_to_mask src))]
    | OF10.SetNwDst dst -> [SetField (OxmIP4Dst (val_to_mask dst))]
    | OF10.SetTpSrc src -> [SetField (OxmTCPSrc (val_to_mask src))]
    | OF10.SetTpDst dst -> [SetField (OxmTCPDst (val_to_mask dst))]
    | OF10.Enqueue _ -> failwith "NYI: Enqueue for OF 0x04"
    | OF10.SetNwTos _ -> failwith "NYI: translate_action SetNwTos"

  (** val to_flow_mod : priority -> Pattern.pattern -> act list -> flowMod **)

  let wildcard_to_mask wc def =
    match wc with
    | WildcardExact a -> val_to_mask a
    | WildcardPartial (v, m) -> {m_value = v; m_mask = Some m}
    | WildcardAll -> {m_value = def; m_mask = Some def}
    | WildcardNone -> {m_value = def; m_mask = Some def}

  let pattern_to_oxm_match pat = 
    let { OpenFlow0x01_Core.dlSrc = dlSrc;
          dlDst = dlDst;
          dlTyp = dlTyp;
          dlVlan = dlVlan;
          dlVlanPcp = dlVlanPcp;
          nwSrc = nwSrc;
          nwDst = nwDst;
          nwProto = nwProto;
          nwTos = nwTos;
          tpSrc = tpSrc;
          tpDst = tpDst;
          inPort = inPort } = pat in
    (* 0 is the all wildcard *)
    ((match dlSrc with Some a -> [OxmEthSrc (val_to_mask a)] | _ -> [])
     @ (match dlTyp with Some t -> [OxmEthType t] | _ -> [])
     @ (match dlDst with Some a -> [ OxmEthDst (val_to_mask a)] | _ -> [])
     @ (match dlVlan with
         | Some (Some a) -> [ OxmVlanVId (val_to_mask a)]
         (* Must be empty list. Trying to get cute and use a wildcard mask confuses the switch *)
         | None -> []
         | Some None -> [OxmVlanVId {m_value=0; m_mask=None}])
     (* VlanPCP requires exact non-VLAN_NONE match on Vlan *)
     @ (match (dlVlanPcp, dlVlan) with (Some a, Some _) -> [ OxmVlanPcp a] | _ -> [])
     @ (match nwSrc with Some a -> [ OxmIP4Src ({m_value = a.OpenFlow0x01_Core.m_value;
                                                 m_mask = a.OpenFlow0x01_Core.m_mask}) ] | _ -> [])
     @ (match nwDst with Some a -> [ OxmIP4Dst ({m_value = a.OpenFlow0x01_Core.m_value;
                                                 m_mask = a.OpenFlow0x01_Core.m_mask})] | _ -> [])
     @ (match inPort with Some p -> [OxmInPort (Int32.of_int p)] | _ -> []),
     (* If IP addrs are set, must be IP EthType. Predicate not currently in compiler *)
     (* @ (match (nwSrc, nwDst) with  *)
     (*   | (Wildcard.WildcardExact t, _) *)
     (*   | (_, Wildcard.WildcardExact t) -> [OxmEthType 0x800]  *)
     (*   | (_,_) -> []) *)
     match inPort with
     | Some p -> Some (Int32.of_int p)
     | _ -> None)

  let get_inport = List.fold_left (fun acc oxm -> 
      match oxm with
      | OxmInPort pp -> Some pp
      | _ -> acc) None

  let set upd mk lst = match upd with
    | Some (_,nw) ->
      (mk nw) :: lst
    | None ->
      lst

  let unset upd mk lst = match upd with
    | Some (Some(od),_) ->
      (mk od) :: lst
    | Some (None,_) ->
      lst
    | None ->
      lst

  let modify out =
    set out.outDlSrc (fun x -> SetField (OxmEthSrc (val_to_mask x)))
      (set out.outDlDst (fun x -> SetField (OxmEthDst (val_to_mask x)))
         ((fun lst -> match out.outDlVlan with
             | Some (Some _, Some x) -> SetField (OxmVlanVId (val_to_mask x)) :: lst
             | Some (None, Some vlan) -> [PushVlan; SetField (OxmVlanVId (val_to_mask vlan))] @ lst
             | Some (Some _, None) -> PopVlan :: lst
             | Some (None, None) -> lst
             | None -> lst)
            (set out.outDlVlanPcp (fun x -> SetField (OxmVlanPcp x))
               (set out.outNwSrc (fun x -> SetField (OxmIP4Src (val_to_mask x)))
                  (set out.outNwDst (fun x -> SetField (OxmIP4Dst (val_to_mask x))) [])))))

  let unmodify out =
    unset out.outDlSrc (fun x -> SetField (OxmEthSrc (val_to_mask x)))
      (unset out.outDlDst (fun x -> SetField (OxmEthDst (val_to_mask x)))
         ((fun lst -> match out.outDlVlan with
             | Some (Some (Some vlan), Some x) -> SetField (OxmVlanVId (val_to_mask vlan)) :: lst
             | Some (Some (None), Some x) -> PopVlan :: lst
             | Some (None, Some vlan) -> PopVlan :: lst
             | Some (Some (Some vlan), None) -> [PushVlan; SetField (OxmVlanVId (val_to_mask vlan))] @ lst
             | Some (Some (None), None) -> lst
             | Some (None, None) -> lst
             | None -> lst)
            (unset out.outDlVlanPcp (fun x -> SetField (OxmVlanPcp x))
               (unset out.outNwSrc (fun x -> SetField (OxmIP4Src (val_to_mask x)))
                  (unset out.outNwDst (fun x -> SetField (OxmIP4Dst (val_to_mask x))) [])))))

  let nc_port_to_of p = match p with
    | P.Physical p -> PhysicalPort (to_of_portId p)
    | P.All -> AllPorts
    | P.Here -> InPort
    | _ -> failwith "nc_port_to_of: Don't know how to handle this port type"

  let output_to_of inp out = match out.outPort with
    | P.Here -> [] (* Fishy, IMO. Shouldn't this be InPort? *)
    | P.All -> modify out @ (Output AllPorts)
                            :: unmodify out
    | P.Physical pt ->
      modify out @
        (( match inp with
            | Some pt' when (=) pt' pt ->
              Output InPort
            | _ ->
              Output (PhysicalPort (to_of_portId pt))) ::
           (unmodify out))
    | _ -> failwith "output_to_of: Don't know how to handle this port type"

  let atom_to_of inp atom = match atom with
    | SwitchAction out -> output_to_of inp out
    | ControllerAction _ -> [ Output (Controller 65535) ]
    | ControllerQuery _ -> []
    | LeaveBufferedAction -> []

  let as_actionSequence1 inp act = 
    let of_atoms = Frenetic_List.concat_map (atom_to_of inp) act in
    let controller_atoms, not_controller_atoms =
      List.partition
        (function | Output (Controller _) -> true | _ -> false)
        of_atoms in
    if List.length controller_atoms > 0 then
      not_controller_atoms @ [List.hd controller_atoms]
    else
      not_controller_atoms

  let as_actionSequence inp acts = 
    List.map (as_actionSequence1 inp) acts

  let to_rule (pattern, action, meta) =
    let match_, inport = NetCore_Pattern.to_match0x04 pattern in
    (match_, as_actionSequence inport action)

  let flow_table_of_policy sw pol0 =
    List.map to_rule (NetCoreCompiler.compile_pol pol0 sw)
end
