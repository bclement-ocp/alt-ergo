module type Store = sig
  type -'a t constraint 'a = [< `W | `R ]

  val create : unit -> [ `W | `R ] t

  val unsafe : 'a t -> [ `W | `R ] t
end

module type Snapshot = sig
  type -'a store constraint 'a = [< `W | `R ]

  type t

  val capture : [> `R ] store -> t

  val restore : [> `W ] store -> t -> unit
end

module Atomic = struct
  module type S = sig
    type -'a store constraint 'a = [< `W | `R ]

    type t

    val create : [ `W | `R ] store -> t

    val read : t -> ([ `R ] store -> 'a) -> 'a

    val write : t -> ([ `R | `W ] store -> 'a) -> t * 'a
  end

  module Make(Snap : Snapshot) : S with type -'a store = 'a Snap.store = struct
    type -'a store = 'a Snap.store

    type t = [ `R | `W ] store * Snap.t

    let create store = (store, Snap.capture store)

    let read (store, snap) f =
      Snap.restore store snap;
      f (store :> [ `R ] store)

    let write (store, snap) f =
      try
        Snap.restore store snap;
        let result = f store in
        (store, Snap.capture store), result
      with e ->
        Snap.restore store snap;
        raise e
  end
end

module type Ref = sig
  type 'a store constraint 'a = [< `W | `R ]

  type 'a t

  val make : 'a -> 'a t

  val get : [> `R ] store -> 'a t -> 'a

  val set : [> `W ] store -> 'a t -> 'a -> unit
end

module Historical : sig
  include Store

  module Ref : Ref with type -'a store = 'a t

  module Snapshot : Snapshot with type -'a store = 'a t

  module Atomic : Atomic.S with type -'a store = 'a t
end = struct
  (* The type of generational values, i.e. values tagged with a generation. *)
  type 'a gen = { mutable v : 'a ; mutable g : int }

  (* A reference is simply a generational value. *)
  type 'a rref = 'a gen

  let[@inline] get_value (r : 'a rref) : 'a = r.v

  let[@inline] set_value (r : 'a rref) (v : 'a) : unit = r.v <- v

  let[@inline] get_gen (r : 'a rref) : int = r.g

  let[@inline] set_gen (r : 'a rref) (g : int) : unit = r.g <- g

  (* The snapshot type is a persistent reference *)
  type snapshot = data ref

  and data =
    | Memory
    | Diff :
        { r : 'a rref
        ; mutable v : 'a
        ; mutable g : int
        ; mutable next : snapshot }
        -> data

  (* The store is a generational snapshot *)
  type -'a t = snapshot gen constraint 'a = [< `W | `R ]

  let create () = { v = ref Memory ; g = 0 }

  let unsafe s = s

  module Snapshot : Snapshot with type -'a store = 'a t = struct
    type -'a store = 'a t

    type t = snapshot

    let capture (s : [> `R ] store) : snapshot =
      (* Capturing a snapshot increases the generation, because we can observe
         the current state *)
      s.g <- s.g + 1;
      s.v

    (* Baker's [reroot] for reference stores *)
    let rec reroot (t : snapshot) : unit =
      match !t with
      | Memory -> ()
      | Diff ({ r; v; g; next = t' } as d) as n ->
        reroot t';
        d.v <- get_value r;
        d.g <- get_gen r;
        set_value r v;
        set_gen r g;
        d.next <- t;
        t := Memory;
        t' := n

    let restore (s : [> `W ] store) (t : snapshot) : unit =
      (* Restoring also increases the generation, because we could go back and
         so the current state can be rerooted to *)
      reroot t;
      s.v <- t;
      s.g <- s.g + 1
  end

  module Ref : Ref with type -'a store = 'a t = struct
    type -'a store = 'a t

    type 'a t = 'a rref

    let make (v : 'a) : 'a rref = { v ; g = -1 }

    let get (_ : [> `R ]store) : 'a t -> 'a = get_value

    let set (s : [> `W ]store) (r : 'a t) (v : 'a) : unit =
      let g = get_gen r in
      if s.g = g then
        set_value r v
      else
        let v' = get_value r in
        set_value r v;
        set_gen r s.g;
        let next = ref Memory in
        s.v := Diff { r; v = v'; g; next };
        s.v <- next
  end

  module Atomic = Atomic.Make(Snapshot)
end
