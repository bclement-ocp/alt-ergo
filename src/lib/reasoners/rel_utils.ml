(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module X = Shostak.Combine
module MX = Shostak.MXH
module SX = Shostak.SXH
module L = Xliteral
module LR = Uf.LX
module SR = Set.Make(
  struct
    type t = X.r L.view
    let compare a b = LR.compare (LR.make a) (LR.make b)
  end)

(** [assume_nontrivial_eqs eqs la] can be used by theories to remove from the
    equations [eqs] both duplicates and those that are implied by the
    assumptions in [la]. *)
let assume_nontrivial_eqs
    (eqs : X.r Sig_rel.input list)
    (la : X.r Sig_rel.input list)
  : X.r Sig_rel.fact list =
  let la =
    List.fold_left (fun m (a, _, _, _) -> SR.add a m) SR.empty la
  in
  let eqs, _ =
    List.fold_left
      (fun ((eqs, m) as acc) ((sa, _, _, _) as e) ->
         if SR.mem sa m then acc else e :: eqs, SR.add sa m
      )([], la) eqs
  in
  List.rev_map (fun (sa, _, ex, orig) -> Sig_rel.LSem sa, ex, orig) eqs

(* The type of delayed functions. A delayed function is given an [Uf.t] instance
   for resolving expressions to semantic values, the operator to compute, and a
   list of expressions as argument.

   It returns a semantic value, and an explanation for why the operator applied
   to the arguments is equal to the result (usually derived from the
   explanations from [Uf.find]). *)
type delayed_fn =
  Uf.t -> Symbols.operator -> Expr.t list -> (X.r * Explanation.t) option

let delay1 embed is_mine f uf op = function
  | [ t ] -> (
      let r, ex = Uf.find uf t in
      match f op (embed r) with
      | Some v -> Some (is_mine v, ex)
      | None -> None
    )
  | _ -> assert false

let delay2 embed is_mine f uf op = function
  | [ t1; t2 ] -> (
      let r1, ex1 = Uf.find uf t1 in
      let r2, ex2 = Uf.find uf t2 in
      match f op (embed r1) (embed r2) with
      | Some v -> Some (is_mine v, Explanation.union ex1 ex2)
      | None -> None
    )
  | _ -> assert false

(** The [Delayed] module can be used by relations that deal with partially
    interpreted functions. It will introduce the equalities between a function
    and its interpreted value as soon as the value of its arguments become
    known.

    To avoid issues with eager splitting, functions are not computed
    on case splits unless model generation is enabled. *)
module Delayed : sig
  type t

  (** [create dispatch] creates a new delayed structure for the symbols handled
      by [dispatch].

      [dispatch] must be pure. *)
  val create : (Symbols.operator -> delayed_fn option) -> t

  (** [add env uf r t] checks whether the term [t] is a delayed function and if
      so either adds it to the structure or evaluates it immediately if
      possible, in which case a new equality with corresponding explanation is
      returned.

      [r] must be the semantic value associated with [t].

      [add] can be called directly with the arguments passed to a relation's
      [add] function. *)
  val add : t -> Uf.t -> X.r -> Expr.t -> t * (X.r L.view * Explanation.t) list

  (** [update env uf r orig eqs] checks whether [r] is an argument of a
      registered delayed function and, if so, tries to compute the corresponding
      delayed function. If all the function's arguments are constants, the
      resulting equality is accumulated into [eqs].

      [update] should be called with the left-hand side of [Eq] literals that
      are [assume]d by a relation. *)
  val update :
    t -> Uf.t -> X.r -> X.r -> Th_util.lit_origin ->
    X.r Sig_rel.input list -> X.r Sig_rel.input list

  (** [assume] is a simple wrapper for [update] that is compatible with the
      [assume] signature of a relation. *)
  val assume : t -> Uf.t -> X.r Sig_rel.input list -> t * X.r Sig_rel.result
end = struct
  module OMap = Map.Make(struct
      type t = Symbols.operator

      let compare = Symbols.compare_operators
    end)

  type t = {
    dispatch : Symbols.operator -> delayed_fn option ;
    used_by : Expr.Set.t OMap.t MX.t ;
  }

  let create dispatch = { dispatch; used_by = MX.empty }

  let add ({ dispatch; used_by } as env) uf r t =
    (* Note: we dispatch on [Op] symbols, but it could make sense to dispatch on
       a separate constructor for explicitely delayed terms. *)
    match Expr.term_view t with
    | { f = Op f; xs; _ } -> (
        match dispatch f with
        | None -> env, []
        | Some fn ->
          match fn uf f xs with
          | Some (r', ex) ->
            if X.equal r' r then
              (* already simplified by [X.make] *)
              env, []
            else
              env, [L.Eq(r', r), ex]
          | None ->
            let used_by =
              List.fold_left (fun used_by x ->
                  MX.update (Uf.make uf x) (fun sm ->
                      let sm = Option.value ~default:OMap.empty sm in
                      Option.some @@
                      OMap.update f (fun se ->
                          let se = Option.value ~default:Expr.Set.empty se in
                          Some (Expr.Set.add t se)) sm) used_by) used_by xs
            in { env with used_by }, []
      )
    | _ -> env, []

  let update { dispatch; used_by } uf r1 eqs =
    match MX.find r1 used_by with
    | exception Not_found -> eqs
    | sm ->
      OMap.fold (fun sy se eqs ->
          let fn =
            (* The [fn] must be present because we only add symbols to
               [used_by] if they are in the dispatch table. *)
            Option.get (dispatch sy)
          in
          Expr.Set.fold (fun t eqs ->
              let { Expr.xs; f; _ } = Expr.term_view t in
              assert (Symbols.equal (Op sy) f);
              match fn uf sy xs with
              | Some (r, ex) ->
                (L.Eq (X.term_embed t, r), None, ex, Th_util.Other) :: eqs
              | None -> eqs) se eqs) sm eqs

  let update env uf r1 r2 orig eqs =
    (* The `Subst` origin is used when `r1 -> r2` is added in the union-find, so
       we want to be propagating the constant on the RHS.

       The other origins are subsumed. *)
    match orig with
    | Th_util.Subst when X.is_constant r2 -> update env uf r1 eqs
    | _ -> eqs


  let assume env uf la =
    let eqs =
      List.fold_left (fun eqs (a, _root, _expl, orig) ->
          match a with
          | Xliteral.Eq (r1, r2) -> update env uf r1 r2 orig eqs
          | _ -> eqs
        ) [] la
    in
    env, { Sig_rel.assume = assume_nontrivial_eqs eqs la; remove = [] }
end

module type Domain = sig
  type t
  (** The type of domains for a single value.

      This is an abstract type that is instanciated by the theory. Note that
      it is expected that this type can carry explanations. *)

  val equal : t -> t -> bool
  (** [equal d1 d2] returns [true] if the domains [d1] and [d2] are
      identical.  Explanations should not be taken into consideration, i.e.
      two domains with different explanations but identical semantics content
      should compare equal. *)

  val pp : t Fmt.t
  (** Pretty-printer for domains. *)

  exception Inconsistent of Explanation.t
  (** Exception raised by [intersect] when an inconsistency is detected. *)

  val create : X.r -> t
  (** [create r] creates a new domain for the possible values of [r].
      Depending on the shape of [r], this can be an arbitrarily precise
      domain, up to being a singleton if [r] has a known value. *)

  val add_explanation : ex:Explanation.t -> t -> t
  (** [add_explanation ~ex d] adds the justification [ex] to the domain d. The
      returned domain is identical to the domain of [d], only the
      justifications are changed. *)

  val intersect : ex:Explanation.t -> t -> t -> t
  (** [intersect ~ex d1 d2] returns a new domain [d] that subsumes both [d1]
      and [d2]. The explanation [ex] justifies that the two domains can be
      merged.

      @raise Inconsistent if [d1] and [d2] are not compatible (the
      intersection would be empty). The justification always includes the
      justification [ex] used for the intersection. *)


  val iter_leaves : (X.r -> t -> unit) -> X.r -> t -> unit
  (** [fold_leaves f r t acc] folds [f] over the leaves of [r], deconstructing
      the domain [t] according to the structure of [r].

      It is assumed that [t] already contains any justification required for
      it to apply to [r].

      @raise Inconsistent if [r] cannot possibly be in the domain of [t]. *)

  val map_leaves : (X.r -> t) -> X.r -> t
  (** [map_leaves f r acc] is the "inverse" of [fold_leaves] in the sense that
      it rebuilds a domain for [r] by using [f] to access the domain for each
      of [r]'s leaves. *)
end

module type Domains = sig
  type t
  (** The type of domain maps. A domain map maps each representative (semantic
      value, of type [X.r]) to its associated domain.*)

  type elt
  (** The type of domains contained in the map. Each domain of type [elt]
      applies to a single semantic value. *)

  val pp : t Fmt.t
  (** Pretty-printer for domain maps. *)

  val create : unit -> t
  (** Create a new empty domain map. Domain maps are fully persistent data
      structures, but they use a [builder] cache to improve the performance of
      [modify] and avoid repeated allocations. *)

  val get : X.r -> t -> elt
  (** [get r t] returns the domain currently associated with [r] in [t].

      If no domain is associated with [r] in [t], returns a most general domain
      for [r] based on its structure. *)

  val add : X.r -> t -> t
  (** [add r t] adds a domain for [r] in the domain map. If [r] does not
      already have an associated domain, a fresh domain will be created for
      [r]. *)

  val fold_leaves : (X.r -> elt -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold f t acc] folds [f] over all the domains in [t] that are associated
      with leaves. *)

  exception Inconsistent of Explanation.t
  (** Exception raised by [update], [subst] and [next_pending] when
      an inconsistency is detected. *)

  type builder
  (** An imperative wrapper around domain maps used for efficiently updating the
      domain map (typically for propagation). Obtained using [modify]. *)

  type handle
  (** A handle to a single domain that tracks whether the domain has been
      updated and allows multiple read/write operations on the domain without
      lookups. *)

  val modify : t -> (builder -> 'a) -> 'a * t
  (** [modify t f] creates a new [builder] with the current state of [t] and
      passes it to [f].

      This allows performing multiple updates of [t] at once in an imperative
      style and data structures (e.g. hash tables instead of functional maps).

      The implementation uses a shared builder that is stored on the domains map
      in order to avoid costly allocations each time [modify] is called, and so
      that calling [modify] without actually performing any modifications is
      cheap. This means that it is not possible to nest calls to [modify] on
      domain maps that originates from the same call to [create ()].

      @raise Invalid_argument if there is already an ongoing modification of [t]
        or another domains map that originates from the same [create ()] call as
        [t]. *)

  val handle : ?add:bool -> builder -> X.r -> handle
  (** [handle bld r] returns a handle to the domain associatd with [r].

      If the optional argument [add] is [true], and no domain associated with
      [r] exists, a new domain for [r] is initialized based on its structure.

      @raise Invalid_argument if [add] is [false] and no domain is associated
         with [r] in [bld]. It is a programming error to do so: do not catch
         this exception and fix your code. *)

  val update : ex:Explanation.t -> handle -> elt -> unit
  (** [update r d t] intersects the domain of [r] in [t] with the domain [d].

      {b Soundness}: The domain [d] must already include the justification
      that it applies to [r].

      @raise Inconsistent if this causes the domain associated with [r] to
      become empty. *)

  val ( !! ) : handle -> elt
  (** Return the domain associated with a [handle]. *)

  val subst : ex:Explanation.t -> X.r -> X.r -> builder -> unit
  (** [subst ~ex p v d] replaces all the instances of [p] with [v] in all
      domains, merging the corresponding domains as appropriate.

      The explanation [ex] justifies the equality [p = v].

      @raise Inconsistent if this causes any domain in [d] to become empty. *)

  val next_pending : builder -> X.r option
  (** [choose_changed d] returns a pair [r] such that:

      - The domain associated with [r] has changed since the last time
        [choose_changed] was called.
      - [r] has (by definition) not changed in [d']

      Moreover, prior to returning [r], structural propagation is
      automatically performed.

      More precisely, if [r] is a leaf, the domain of [r] is propagated to any
      semantic value that contains [r] as a leaf according to the structure of
      that semantic value (using [Domain.map_leaves]); if [r] is not a leaf,
      its domain is propagated to any of the leaves it contains.

      We only perform *forward* structural propagation: if structural
      propagation causes a domain of a leaf or parent to be changed, then we
      will perform structural propagation for that leaf or parent once it
      itself is selected by [choose_changed].

      @raise Inconsistent if an inconsistency if detected during structural
      propagation. *)
end

module Domains_make(Domain : Domain) : Domains with type elt = Domain.t =
struct
  type elt = Domain.t

  exception Inconsistent = Domain.Inconsistent

  module HT = Hashtbl.Make(struct
      type t = X.r

      let hash = X.hash

      let equal = X.equal
    end)

  type builder = {
    mutable domains_map : Domain.t MX.t ;
    (** The original [domains] from the snapshot this was created from, minus
        any elements that were removed. *)

    mutable parents_map : SX.t MX.t ;
    (** Map from leaves to the tracked representatives that contains them.
        Updated on adding and substitution. *)

    domains_cache : handle HT.t ;
    (** Cache of domain values for efficient access. Domains are initialized
        from the [domains_map], see the documentation for [handle].  *)

    dirty_cache : handle HT.t ;
    (** Subset of the [domains_cache] that only contains dirty handle, i.e.
        handles for which the domain has been updated and is no longer equal to
        the one stored in the [domains_map].

        This field is automatically updated from the [handle] when it becomes
        dirty. *)

    pending_set : unit HT.t ;
    (** Set of representatives marked as pending, i.e. whose domain has been
        updated since the last propagation.

        Note that pending elements are not guaranteed to be in either of the
        [domains_cache] (if the element was pending in the snapshot) or the
        [domains_map] (if the element was added since the snapshot), but they
        are guaranteed to be in at least one of them.

        This field is automatically updated from the [handle] when it becomes
        pending. *)
  }

  and handle = {
    repr : X.r ;
    (** Semantic value associated with this handle. *)

    mutable domain : Domain.t ;
    (** The domain associated with [repr]. *)

    mutable dirty : bool ;
    (** Dirty flag. If true, the [domain] is not identical to the one in the
        [owner]'s [domain_map] and it will need to be updated in the persistent
        [snapshot]. Otherwise, the [snapshot] does not need to be updated.

        The [dirty] flag is true iff the [repr] is in its [owner]'s
        [dirty_cache] (in which case it must be mapped to this [handle]). *)

    mutable pending : bool ;
    (** Pending flag. If true, the [domain] has been updated since the last
        propagation. Note that [pending] may be [true] while [dirty] is [false]
        if the representative was pending in the original snapshot.

        The [pending] flag is true iff the [repr] is in its [owner]'s
        [pending_set]. *)

    owner : builder
    (** The domains set that contains this handle. Used to automatically update
        the [dirty_cache] and [pending_set] fields from the [handle]. *)
  }

  type t = {
    domains : Domain.t MX.t ;
    (** Map from tracked representatives to their domain *)

    changed : SX.t ;
    (** Representatives whose domain has changed since the last propagation *)

    parents : SX.t MX.t ;
    (** Map from leaves to the *tracked* representatives that contains them *)

    builder : builder option ref ;
  }

  let create () =
    let cell = ref @@ Some
        { domains_map = MX.empty
        ; parents_map = MX.empty
        ; domains_cache = HT.create 17
        ; dirty_cache = HT.create 17
        ; pending_set = HT.create 17
        }
    in
    { domains = MX.empty
    ; changed = SX.empty
    ; parents = MX.empty
    ; builder = cell }

  let pp ppf t =
    Fmt.(iter_bindings ~sep:semi MX.iter
           (box @@ pair ~sep:(any " ->@ ") X.print Domain.pp)
         |> braces
        )
      ppf t.domains


  let modify { domains; changed; parents; builder = cell } f =
    let t =
      match !cell with
      | Some builder ->
        HT.clear builder.domains_cache;
        HT.clear builder.dirty_cache;
        HT.clear builder.pending_set;
        cell := None;
        builder
      | None ->
        (* Can only modify the same domain set once at a time. *)
        invalid_arg "modify"
    in
    t.domains_map <- domains;
    t.parents_map <- parents;
    SX.iter (fun r -> HT.add t.pending_set r ()) changed;
    Fun.protect ~finally:(fun () -> cell := Some t) @@ fun () ->
    let res = f t in
    let domains =
      HT.fold (fun r { domain; dirty; _ } domains ->
          assert dirty;
          MX.add r domain domains
        ) t.dirty_cache t.domains_map
    in
    let changed =
      HT.fold (fun r () changed -> SX.add r changed) t.pending_set SX.empty
    in
    cell := Some t;
    res, { domains; changed; parents = t.parents_map; builder = cell }

  let r_add r parents_map =
    List.fold_left (fun parents_map leaf ->
        MX.update leaf (function
            | Some parents -> Some (SX.add r parents)
            | None -> Some (SX.singleton r)
          ) parents_map
      ) parents_map (X.leaves r)

  let ( !! ) { domain; _ } = domain

  let handle ?(add = false) t r =
    try
      HT.find t.domains_cache r
    with Not_found ->
      let domain, dirty =
        match MX.find r t.domains_map with
        | domain -> domain, false
        | exception Not_found ->
          if not add then invalid_arg "handle";
          t.parents_map <- r_add r t.parents_map;
          Domain.create r, true
      in
      let pending = HT.mem t.pending_set r in
      let handle = { repr = r; domain; dirty; pending; owner = t } in
      HT.add t.domains_cache r handle;
      if dirty then
        HT.add t.dirty_cache r handle;
      handle

  let handle_assert t r =
    try handle t r with Not_found -> assert false

  let set_dirty handle =
    if not handle.dirty then (
      handle.dirty <- true;
      HT.replace handle.owner.dirty_cache handle.repr handle
    )

  let set_pending handle =
    if not handle.pending then (
      handle.pending <- true;
      HT.replace handle.owner.pending_set handle.repr ()
    )

  let update ~ex handle domain =
    let domain = Domain.intersect ~ex handle.domain domain in
    if not (Domain.equal handle.domain domain) then (
      set_dirty handle;
      set_pending handle;
      handle.domain <- domain
    )

  let r_remove r parents_map =
    List.fold_left (fun parents_map leaf ->
        MX.update leaf (function
            | Some parents ->
              let parents = SX.remove r parents in
              if SX.is_empty parents then None else Some parents
            | None -> None
          ) parents_map
      ) parents_map (X.leaves r)

  let subst ~ex rr nrr (t : builder) =
    match MX.find rr t.parents_map with
    | parents ->
      let domains_map, parents_map =
        SX.fold (fun r (domains_map, parents_map) ->
            let domain, r_pending =
              match HT.find t.domains_cache r with
              | { domain; dirty; pending; _ } ->
                HT.remove t.domains_cache r;
                if dirty then
                  HT.remove t.dirty_cache r;
                domain, pending
              | exception Not_found ->
                try MX.find r t.domains_map, HT.mem t.pending_set r
                with Not_found ->
                  (* [r] was in the [parents_map] to it must have a domain *)
                  assert false
            in
            let nr = X.subst rr nrr r in
            let nhandle = handle ~add:true t nr in
            update ~ex nhandle domain;
            if r_pending then (
              set_pending nhandle;
              HT.remove t.pending_set r
            );
            MX.remove r domains_map,
            r_add nr @@ r_remove r @@ parents_map
          ) parents (t.domains_map, t.parents_map)
      in
      t.domains_map <- domains_map;
      t.parents_map <- parents_map
    | exception Not_found -> ()

  let structural_propagation r (t : builder) =
    if X.is_a_leaf r then
      match MX.find r t.parents_map with
      | parents ->
        SX.iter (fun parent ->
            if X.is_a_leaf parent then (
              assert (X.equal r parent)
            ) else
              (* If we are in the [parents_map] we must have a handle. *)
              update ~ex:Explanation.empty (handle_assert t parent) @@
              Domain.map_leaves (fun r -> (handle ~add:true t r).domain) parent
          ) parents
      | exception Not_found -> ()
    else
      let update r d =
        update ~ex:Explanation.empty (handle ~add:true t r) d
      in
      (* Only called on representatives that are in the map, so [handle] cannot
         fail (see [next_pending]). *)
      Domain.iter_leaves update r (handle_assert t r).domain

  let next_pending t =
    let chosen = ref None in
    begin try
        HT.iter (fun r () -> chosen := Some r; raise Exit) t.pending_set
      with Exit -> () end;
    match !chosen with
    | Some r ->
      let handle =
        try
          handle ~add:false t r
        with Not_found ->
          (* Values in the pending_set must have a domain. *)
          assert false
      in
      assert handle.pending;
      handle.pending <- false;
      HT.remove t.pending_set r;
      structural_propagation r t;
      Some r
    | None -> None

  let add r t =
    match MX.find r t.domains with
    | _ -> t
    | exception Not_found ->
      (* Note: we do not need to mark [r] as needing propagation, because no
          constraints applied to it yet. Any constraint that apply to [r] will
          already be marked as pending due to being newly added. *)
      let d = Domain.create r in
      let domains = MX.add r d t.domains in
      let parents = r_add r t.parents in
      { t with domains; parents }

  let get r t =
    (* We need to catch [Not_found] because of fresh terms that can be added
        by the solver and for which we don't call [add]. Note that in this
        case, only structural constraints can apply to [r]. *)
    try MX.find r t.domains with Not_found -> Domain.create r

  let fold_leaves f t acc =
    MX.fold (fun r _ acc ->
        f r (get r t) acc
      ) t.parents acc
end

module type Constraint = sig
  type t
  (** The type of constraints.

      Constraints apply to semantic values of type [X.r] as arguments. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraints. *)

  val compare : t -> t -> int
  (** Comparison function for constraints. The comparison function is
      arbitrary and has no semantic meaning. You should not depend on any of
      its properties, other than it defines an (arbitrary) total order on
      constraint representations. *)

  val fold_args : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_args f c acc] folds function [f] over the arguments of constraint
      [c].

      During propagation, the constraint {b MUST} only look at (and update)
      the domains associated of its arguments; it is not allowed to look at
      the domains of other semantic values. This allows efficient updates of
      the pending constraints. *)

  val subst : X.r -> X.r -> t -> t
  (** [subst p v cs] replaces all the instances of [p] with [v] in the
      constraint.

      {b Note}: Substitution {b MUST} be inert, i.e. substitution {b MUST NOT}
      depend on the result of the substitution applied to the constraint
      arguments.  The new constraint must have the same effect as the old one
      on *any* domain where the substitution has been applied. This is allows
      efficient updates of the pending constraints. *)
end

type 'a explained = { value : 'a ; explanation : Explanation.t }

let explained ~ex value = { value ; explanation = ex }

module Constraints_make(Constraint : Constraint) : sig
  type t
  (** The type of constraint sets. A constraint set records a set of
      constraints that applies to semantic values, and remembers the relation
      between constraints and semantic values.

      The constraints associated with specific semantic values can be notified
      (see [notify]), which is used to only propagate constraints involving
      semantic values whose domain has changed.

      The constraints that have been notified are called "pending
      constraints", and the set thereof is the "pending set". These are
      constraints that need to be propagated, and can be recovered using
      [next_pending]. *)

  val pp : t Fmt.t
  (** Pretty-printer for constraint sets. *)

  val empty : t
  (** The empty constraint set. *)

  val add : ?pending:bool -> ex:Explanation.t -> Constraint.t -> t -> t
  (** [add ~ex c t] adds the constraint [c] to the set [t].

      The explanation [ex] justifies that the constraint [c] holds.

      The constraint is only added to the pending set if it was not already
      active (i.e. previously added). Setting the [pending] optional argument to
      [true] forces the constraint to be marked as pending even if it is already
      active. *)

  val subst : ex:Explanation.t -> X.r -> X.r -> t -> t
  (** [subst ~ex p v t] replaces all instances of [p] with [v] in the
      constraints.

      The explanation [ex] justifies the equality [p = v]. *)

  val notify : X.r -> t -> t
  (** [notify r t] marks all constraints involving [r] (i.e. all constraints
      that have [r] as one of their arguments) as pending.

      This function should be used when the domain of [r] is updated, if
      domains are tracked for all representatives. *)

  val notify_leaf : X.r -> t -> t
  (** [notify_leaf r t] marks all constraints that have [r] as a leaf (i.e.
      all constraints that have at least one argument [a] such that [r] is in
      [X.leaves a]) as pending.

      This function should be used when the domain of [r] is updated, if
      domains are tracked for leaves only. *)

  val fold_args : (X.r -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_args f t acc] folds [f] over all the term representatives that are
      arguments of at least one constraint. *)

  val next_pending : t -> Constraint.t explained * t
  (** [next_pending t] returns a pair [c, t'] where [c] was pending in [t] and
      [t'] is identical to [t], except that [c] is no longer a pending
      constraint.

      @raise Not_found if there are no pending constraints. *)
end = struct
  module CS = Set.Make(struct
      type t = Constraint.t explained

      let compare a b = Constraint.compare a.value b.value
    end)

  type t = {
    args_map : CS.t MX.t ;
    (** Mapping from semantic values to constraints involving them *)

    leaves_map : CS.t MX.t ;
    (** Mapping from semantic values to constraints they are a leaf of *)

    active : CS.t ;
    (** Set of all currently active constraints *)

    pending : CS.t ;
    (** Set of active constraints that have not yet been propagated *)
  }

  let pp ppf { active; _ } =
    Fmt.(
      braces @@ hvbox @@
      iter ~sep:semi CS.iter @@
      using (fun { value; _ } -> value) @@
      box ~indent:2 @@ braces @@
      Constraint.pp
    ) ppf active

  let empty =
    { args_map = MX.empty
    ; leaves_map = MX.empty
    ; active = CS.empty
    ; pending = CS.empty }

  let cs_add c r cs_map =
    MX.update r (function
        | Some cs -> Some (CS.add c cs)
        | None -> Some (CS.singleton c)
      ) cs_map

  let fold_leaves f c acc =
    Constraint.fold_args (fun r acc ->
        List.fold_left (fun acc r -> f r acc) acc (X.leaves r)
      ) c acc

  let add ?(pending = false) ~ex c t =
    let c = explained ~ex c in
    (* Note: use [CS.find] here, not [CS.mem], to ensure we use the same
       explanation for [c] in the [pending] and [active] sets. *)
    match CS.find c t.active with
    | c ->
      if pending then { t with pending = CS.add c t.pending } else t
    | exception Not_found ->
      let active = CS.add c t.active in
      let args_map =
        Constraint.fold_args (cs_add c) c.value t.args_map
      in
      let leaves_map = fold_leaves (cs_add c) c.value t.leaves_map in
      let pending = CS.add c t.pending in
      { active; args_map; leaves_map; pending }

  let cs_remove c r cs_map =
    MX.update r (function
        | Some cs ->
          let cs = CS.remove c cs in
          if CS.is_empty cs then None else Some cs
        | None -> None
      ) cs_map

  let remove c t =
    let active = CS.remove c t.active in
    let args_map =
      Constraint.fold_args (cs_remove c) c.value t.args_map
    in
    let leaves_map = fold_leaves (cs_remove c) c.value t.leaves_map in
    let pending = CS.remove c t.pending in
    { active; args_map; leaves_map; pending }

  let subst ~ex rr nrr t =
    match MX.find rr t.leaves_map with
    | cs ->
      CS.fold (fun c t ->
          let pending = CS.mem c t.pending in
          let t = remove c t  in
          let ex = Explanation.union ex c.explanation in
          add ~pending ~ex (Constraint.subst rr nrr c.value) t
        ) cs t
    | exception Not_found -> t

  let notify r t =
    match MX.find r t.args_map with
    | cs ->
      CS.fold (fun c t -> { t with pending = CS.add c t.pending }) cs t
    | exception Not_found -> t

  let notify_leaf r t =
    match MX.find r t.leaves_map with
    | cs ->
      CS.fold (fun c t -> { t with pending = CS.add c t.pending }) cs t
    | exception Not_found -> t

  let fold_args f c acc =
    MX.fold (fun r _ acc ->
        f r acc
      ) c.args_map acc

  let next_pending t =
    let c = CS.choose t.pending in
    c, { t with pending = CS.remove c t.pending }
end
