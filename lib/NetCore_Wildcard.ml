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
end

module Make (Ord : OrderedType) = struct

  type a = Ord.t

  type t = a wildcard

  (* TODO(adf): update for WildcardPartial *)
  let is_equal x y = match (x, y) with
    | WildcardExact a, WildcardExact b -> Ord.compare a b = 0
    | WildcardAll, WildcardAll -> true
    | WildcardNone, WildcardNone -> true
    | _ -> false

  (* TODO(adf): update for WildcardPartial *)
  let contains x y = match (x, y) with
    | WildcardNone, _ -> true
    | _, WildcardAll -> true
    | WildcardExact a, WildcardExact b -> Ord.compare a b = 0
    | _ -> false

  (* TODO(adf): update for WildcardPartial *)
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
