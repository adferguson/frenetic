open Packet

module type ACTION = NetCore_Action.ACTION

module type CLASSIFIER = sig
  type action

  type t = (NetCore_Types.ptrn * action) list

  val scan : t -> NetCore_Types.port -> packet -> action

  val union : t -> t -> t

  val sequence : t -> t -> t

  val par_actions : action list -> action

  val choice : t -> t -> t

end

module type MAKE = functor (Action : ACTION) ->
sig include CLASSIFIER end
  with type action = Action.t

module Make : MAKE = functor (Action:ACTION) -> struct
  type action = Action.t

  type t = (NetCore_Pattern.t * action) list

  let rec scan' default classifier pt pk = match classifier with
    | [] -> default
    | p :: rest ->
      let (pat, a) = p in
      if NetCore_Pattern.match_packet pt pk pat then a else scan' default rest pt pk

  let scan = scan' Action.drop

  let rec elim_shadowed_helper prefix = function
    | [] -> prefix
    | p :: cf' ->
      let (pat, act) = p in
      if List.exists (fun entry ->
          let (pat', act0) = entry in NetCore_Pattern.contains pat pat') prefix
      then elim_shadowed_helper prefix cf'
      else elim_shadowed_helper (prefix @ ((pat, act) :: [])) cf'

  let elim_shadowed cf =
    elim_shadowed_helper [] cf

  let rec strip_empty_rules = function
    | [] -> []
    | p :: cf0 ->
      let (pat, acts) = p in
      if NetCore_Pattern.is_empty pat
      then strip_empty_rules cf0
      else (pat, acts) :: (strip_empty_rules cf0)

  let rec condense_contained tbl = match tbl with
    | [] -> []
    | (pat1, act1) :: lst -> 
      match condense_contained lst with
      | [] -> (pat1, act1) :: []
      | (pat2, act2) :: rest -> 
        if NetCore_Pattern.contains pat1 pat2 && Action.is_equal act1 act2 then
          (pat2, act2) :: rest
        else
          (pat1, act1) :: (pat2, act2) :: rest

  let opt tbl =
    condense_contained (elim_shadowed (strip_empty_rules tbl))

  let inter_entry cl (pat, act) = 
    List.fold_right 
      (fun (pat',act') acc ->
         (NetCore_Pattern.inter pat pat', Action.par_action act act') :: acc) cl []

  let inter_no_opt cl1 cl2 =
    List.fold_right (fun v acc -> (inter_entry cl2 v) @ acc) cl1 []

  let union_no_opt cl1 cl2 =
    opt ((inter_no_opt cl1 cl2) @ cl1 @ cl2)

  let rec par_actions = function
    | [] -> Action.drop
    | act :: lst' -> Action.par_action act (par_actions lst')

  let seq tbl1 tbl2 sw pt pk bf =
    Action.seq_action (scan tbl1 pt pk)
      (par_actions
         (List.map (fun (sw,pt0,pk0,bf0) -> scan tbl2 pt0 pk0)
            (Action.apply_action (scan tbl1 pt pk) (sw, pt, pk, bf))))

  let union tbl1 tbl2 =
    union_no_opt tbl1 tbl2

  let inter tbl1 tbl2 =
    opt (inter_no_opt tbl1 tbl2)

  let rec unions = function
    | [] -> []
    | tbl :: lst' -> union_no_opt tbl (unions lst')

  (* [p1] is the domain restriction from the first table in the sequence.
     [a1] is ???
     [atom] is the first action that was applied.
  *)
  let rec sequence_atom_no_opt p1 atom tbl2 = match tbl2 with
    | [] -> []
    | (p2,a) :: tbl2' ->
      (NetCore_Pattern.inter
         p1
         (NetCore_Pattern.inter
            (Action.domain atom)
            (Action.sequence_range atom p2)),
       Action.seq_action (Action.to_action atom) a) 
      :: (sequence_atom_no_opt p1 atom tbl2')

  let rec sequence_no_opt tbl1 tbl2 =
    match tbl1 with
    | [] -> []
    | (p,a) :: tbl1' ->
      match Action.atoms a with
      | [] -> (p, Action.drop) :: (sequence_no_opt tbl1' tbl2)
      | atoms ->
        let sequenced_atoms = 
          (unions 
             (List.map 
                (fun atom -> sequence_atom_no_opt p atom tbl2) atoms)) in
        sequenced_atoms @ (sequence_no_opt tbl1' tbl2)

  let sequence tbl1 tbl2 =
    opt (sequence_no_opt tbl1 tbl2)

  let alt_entry cl (pat, act) = 
    List.fold_right 
      (fun (pat',act') acc ->
        (NetCore_Pattern.inter pat pat', Action.alt_action act act') :: acc) cl []

  let alt_no_opt cl1 cl2 =
    opt ((List.fold_right (fun v acc -> (alt_entry cl2 v) @ acc) cl1 []) @ cl1 @ cl2)

  let choice = alt_no_opt

 end
