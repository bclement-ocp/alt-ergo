type 'a view = LTerm of Expr.t | LSem of 'a

val pp_view : 'a Fmt.t -> 'a view Fmt.t

val hash_view : ('a -> int) -> 'a view -> int

val equal_view : ('a -> 'a -> bool) -> 'a view -> 'a view -> bool

val compare_view : ('a -> 'a -> int) -> 'a view -> 'a view -> int

val neg_view : ('a -> 'a) -> 'a view -> 'a view

module type S = sig
  type elt

  type t

  val make : elt view -> t

  val view : t -> elt view

  val pp : t Fmt.t

  val hash : t -> int

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val neg : t -> t

  val normal_form : t -> t * bool

  module Table : Hashtbl.S with type key = t

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t
end

module Make(Sem : Xliteral.S) : S with type elt = Sem.t
