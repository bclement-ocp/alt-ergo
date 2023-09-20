module type Store = sig
  type -'a t

  module Ref : sig
    type 'a store = 'a t

    type 'a t

    val make : 'a -> 'a t

    val get : [> `R ] store -> 'a t -> 'a

    val set : [> `W ] store -> 'a t -> 'a -> unit
  end

  (** [create ()] initializes a new store. *)
  val create : unit -> [ `W | `R | `S ] t

  val unsafe : _ t -> [ `W | `R | `S ] t

  (** [try' store f] is equivalent to:

      ```ocaml
      let snapshot = capture store in
      try
        f store
      with e ->
        restore store snapshot;
        raise e
      ```

      but allows optimizations exploiting the affinity of `snapshot` (it is
      restored at most once).
  *)
  val try' : [> `R | `W] t -> ([`R | `W] t -> 'a) -> 'a

  (** [protect store f] is equivalent to:

      ```ocaml
      let snapshot = capture store in
      Fun.protect (fun () -> f store)
        ~finally:(fun () -> restore store snapshot)
      ```

      but allows optimizations exploiting the linearity of `snapshot` (it is
      always restored). *)
  val protect : [> `R | `W] t -> ([`R | `W] t -> 'a) -> 'a

  (** Snapshots allow low-level control over the store's state.

      Note that [try'] and [protect] make the inner store non-snapshottable.
  *)
  type snapshot

  (** [capture store] returns a new snapshot corresponding to the current state
      of the memory associated with the store [store].

      To capture the store, it must be snapshottable ([`S] flag).
  *)
  val capture : [> `R | `S ] t -> snapshot

  (** [restore store snapshot] resets the memory associated with store [store]
      to the state it was in when the [snapshot] was captured.

      [snapshot] must be a snapshot of the [store], the [store] must be
      snapshottable, and the [store] must not be currently used by [try'] or
      [protect]. *)
  val restore : [> `S | `W ] t -> snapshot -> unit
end

module Historical : Store = struct
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
  type -'a t = snapshot gen

  type -'a store = 'a t

  let create () = { v = ref Memory ; g = 0 }

  let unsafe s = s

  let capture (s : [> `R ] store) : snapshot =
    (* Capturing a snapshot increases the generation, because we can observe
        the current state *)
    s.g <- s.g + 1;
    s.v

  (* Baker's [reroot] for reference stores *)
  let[@landmark] rec reroot (t : snapshot) : unit =
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

  (* The resulting snapshot must only be created once! *)
  let capture1 ({ g; _ } as s) =
    capture s, g

  let restore1 s (t, g) =
    assert (s.g = g + 1);
    reroot t;
    s.v <- t;
    s.g <- g

  let try' store f =
    let snapshot = capture1 store in
    try
      f store
    with e ->
      restore1 store snapshot;
      raise e

  let protect store f =
    let snapshot = capture store in
    Fun.protect (fun () -> f store)
      ~finally:(fun () -> restore store snapshot)

  module Ref = struct
    type -'a store = 'a t

    type 'a t = 'a rref

    let make (v : 'a) : 'a rref = { v ; g = -1 }

    let get (_ : [> `R ] store) : 'a t -> 'a = get_value

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
end
