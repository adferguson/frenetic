module OF = OpenFlow0x01_Core

type 'a wildcard = 
  | WildcardExact of 'a
  | WildcardPartial of 'a * 'a
  | WildcardAll
  | WildcardNone

module type Wildcard = sig

  type a

  type t = a wildcard

  val is_equal : t -> t -> bool
  val contains : t -> t -> bool
  val inter : t -> t -> t
  val is_all : t -> bool
  val is_empty : t -> bool
  val is_exact : t -> bool
  val to_option : t -> a option option
  val to_masked_option : t -> a OF.mask option option
end

module type OrderedType = sig
  type t 
  val compare : t -> t -> int

  (* compare two (value, mask) pairs *)
  val masked_inter : t * t -> t * t -> (t * t) option
  (* returns the value representing "zero" to faciliate
     comparison between WildcardExact and WilcardPartial *)
  val zero : t
end

module Make (Ord : OrderedType) = struct

  type a = Ord.t

  type t = a wildcard

  let is_equal x y = match (x, y) with
    | WildcardExact a, WildcardExact b -> Ord.compare a b = 0
    | WildcardAll, WildcardAll -> true
    | WildcardNone, WildcardNone -> true
    | WildcardPartial (v1, m1), WildcardPartial (v2, m2) ->
        (Ord.compare v1 v2 = 0) && (Ord.compare m1 m2 = 0)
    | _ -> false

  let contains x y = match (x, y) with
    | WildcardNone, _ -> true
    | _, WildcardAll -> true
    | WildcardExact a, WildcardExact b -> Ord.compare a b = 0
    | WildcardPartial (v, m), WildcardExact b ->
      (match Ord.masked_inter (v, m) (b, Ord.zero) with
         | Some _ -> true
         | None -> false)
    | WildcardExact a, WildcardPartial (v, m) ->
      (match Ord.masked_inter (a, Ord.zero) (v, m) with
         | Some _ -> true
         | None -> false)
    | WildcardPartial (v1, m1), WildcardPartial (v2, m2) ->
      (match Ord.masked_inter (v1, m1) (v2, m2) with
         | Some (m, v) -> true
         | None -> false)
    | _ -> false

  let inter x y = match (x, y) with
    | WildcardNone, _ -> WildcardNone
    | _, WildcardNone -> WildcardNone
    | WildcardAll, y -> y
    | x, WildcardAll -> x
    | WildcardExact a, WildcardExact b -> 
      if Ord.compare a b = 0 then
        WildcardExact b
      else 
        WildcardNone
    | WildcardPartial (v, m), WildcardExact b ->
      (match Ord.masked_inter (v, m) (b, Ord.zero) with
         | Some _ -> WildcardExact b
         | None -> WildcardNone)
    | WildcardExact a, WildcardPartial (v, m) ->
      (match Ord.masked_inter (a, Ord.zero) (v, m) with
         | Some _ -> WildcardExact a
         | None -> WildcardNone)
    | WildcardPartial (v1, m1), WildcardPartial (v2, m2) ->
      (match Ord.masked_inter (v1, m1) (v2, m2) with
         | Some (m, v) -> WildcardPartial (m, v)
         | None -> WildcardNone)

  let is_all x = match x with
    | WildcardAll -> true
    | _ -> false

  let is_empty x = match x with
    | WildcardNone -> true
    | _ -> false


  let is_exact x = match x with
    | WildcardExact _ -> true
    | _ -> false

  let to_option x = match x with
    | WildcardAll -> Some None
    | WildcardPartial (v, m) -> failwith "invalid"
    | WildcardExact a -> Some (Some a)
    | WildcardNone -> None

  let to_masked_option x = match x with
    | WildcardAll -> Some None
    | WildcardExact a -> Some (Some {OF.m_value = a; m_mask = None})
    | WildcardPartial (m, n) -> Some (Some {OF.m_value = m; m_mask = Some n})
    | WildcardNone -> None

end

let to_string_exact ts label = function
  | WildcardExact a -> 
    Format.sprintf "@[%s = %s@]" label (ts a)
  | WildcardPartial (m, n) ->
    Format.sprintf "@[%s = %s/%s@]" label (ts m) (ts n)
  | WildcardAll -> ""
  | WildcardNone -> ""
