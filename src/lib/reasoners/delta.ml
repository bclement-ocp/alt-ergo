(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2024 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module Log = struct
  let debug k =
    k Format.printf
end

module type WEIGHT = sig
  type t

  val compare : t -> t -> int

  val add : t -> t -> t

  val zero : t

  val sub : t -> t -> t
end

module type PATH = sig
  type t

  val empty : t

  val append : t -> t -> t
end

module Pqueue(V : Graph.Sig.ORDERED_TYPE_DFT) : sig
  type t

  val create : int -> t

  val insert : t -> V.t -> unit

  val pop_min : t -> V.t
  (** @raises Not_found *)
end = struct
  type entry = { value : V.t ; mutable index : int }

  let entry value = { value ; index = -1 }

  module H = Heap.MakeRanked(struct
      type t = entry

      let index e = e.index

      let set_index e i = e.index <- i

      let compare x y = V.compare x.value y.value
    end)

  type t = H.t

  let create n = H.create n (entry V.default)

  let insert h v = H.insert h (entry v)

  let pop_min h = (H.pop_min h).value
end

module type REF = sig
  type 'a t

  val create : 'a -> 'a t

  val get : 'a t -> 'a

  val set : 'a t -> 'a -> 'a t
end

module Impl
    (W : WEIGHT)
    (P : PATH)
    (B : Graph.Builder.S with type G.E.label = W.t * P.t)
    (S : Set.S with type elt = B.G.V.t)
    (HM : Graph.Blocks.HM with type key = B.G.V.t)
    (R : REF)
    (PP : sig val vertex : B.G.V.t Fmt.t val edge : B.G.E.t Fmt.t end)=
struct
  let (~-) = W.sub W.zero

  let ( + ) = W.add

  let ( - ) = W.sub

  module G = B.G

  type improvement = { inf_improved : S.t ; sup_improved : S.t }

  type g =
    { graph : G.t
    ; potentials : W.t HM.t }

  let potential g v =
    try HM.find v g.potentials with Not_found -> W.zero

  type graph_ops =
    { potential : g -> G.V.t -> W.t
    ; iter_succ_e : (G.E.t -> unit) -> G.t -> G.V.t -> unit
    ; src : G.E.t -> G.V.t
    ; dst : G.E.t -> G.V.t
    ; append : P.t -> P.t -> P.t }

  let forward_ops =
    { src = G.E.src
    ; dst = G.E.dst
    ; iter_succ_e = G.iter_succ_e
    ; potential = potential
    ; append = P.append }

  let backward_ops =
    { src = G.E.dst
    ; dst = G.E.src
    ; iter_succ_e = G.iter_pred_e
    ; potential = (fun g v -> -potential g v)
    ; append = (fun p q -> P.append q p) }

  let weight e = fst @@ G.E.label e

  let path e = snd @@ G.E.label e

  let reduced_cost g e =
    potential g (G.E.src e) + weight e - potential g (G.E.dst e)

  module Elt = struct
    type t = { target : G.V.t ; weight : W.t ; path : P.t }

    let compare x y = W.compare x.weight y.weight

    let default =
      { target = Obj.magic 0 (* gruik *); weight = W.zero ; path = P.empty }
  end

  module H = Pqueue(Elt)

  module Vtbl = Hashtbl.Make(G.V)

  exception Negative_cycle of P.t

  let restore_potential g e =
    let x = G.E.src e and y = G.E.dst e and k = weight e in

    (* entries with updated potential, i.e. where \pi' <> \pi *)
    let visited = Vtbl.create 97 in

    (* \gamma in XXX; missing entries have \gamma = 0

       [shortest t] is the length of the shortest path from [src edge] to [t]
       that starts with [edge] *)
    let shortest = Vtbl.create 97 in

    (* Min-queue for argmin *)
    let pq = H.create 97 in

    let rec loop () =
      match H.pop_min pq with
      | exception Not_found ->
        (* All slacks are positive, we found a valid potential *)
        ()
      | elt ->
        let s = elt.target in
        if not (Vtbl.mem visited s) then (
          (* w is \gamma(s) *)
          let w = elt.weight in
          if W.compare w W.zero >= 0 then
            (* All slacks are positive, we found a valid potential *)
            ()
          else if G.V.equal s x then
            (* Found a negative cycle *)
            raise (Negative_cycle elt.path)
          else (
            Vtbl.replace visited s ();

            (* Fix the negative slack for s then propagate forward *)
            let new_potential_s = potential g s + w in
            G.iter_succ_e (fun edge ->
                let t = G.E.dst edge in
                if not (Vtbl.mem visited t) then (
                  let dt = new_potential_s + weight edge - potential g t in
                  let improved =
                    try W.compare dt (Vtbl.find shortest t) < 0
                    with Not_found -> true
                  in
                  if improved then (
                    Vtbl.replace shortest t dt;
                    H.insert pq
                      { weight = dt
                      ; target = t
                      ; path = P.append elt.path (path edge) }
                  )
                )
              ) g.graph s
          )
        );

        loop ()
    in

    let dx = potential g x + k - potential g y in
    H.insert pq
      { weight = dx
      ; target = y
      ; path = path e };
    Vtbl.replace shortest y dx;

    loop ();

    let new_potential =
      Vtbl.fold (fun v () new_potential ->
          let slack = try Vtbl.find shortest v with Not_found -> assert false in
          assert (W.compare slack W.zero < 0);
          HM.add v (potential g v + slack) new_potential
        ) visited g.potentials
    in

    { g with potentials = new_potential }

  (* Must not have an edge with the same source and destination *)
  let unsafe_add_edge g e =
    let g = { g with graph = B.add_edge_e g.graph e } in

    if W.compare (reduced_cost g e) W.zero < 0 then
      restore_potential g e
    else
      g

  let add_edge_e g e =
    let x = G.E.src e and y = G.E.dst e in
    (* No need to actually add reflexive edges, but need to check them for
       consistency *)
    if G.V.equal x y then
      if W.compare (weight e) W.zero >= 0 then
        g
      else
        raise (Negative_cycle (path e))
    else
      match G.find_edge g.graph x y with
      | old when W.compare (weight old) (weight e) < 0 ->
        (* We already have a tighter constraint *)
        assert (W.compare (reduced_cost g e) W.zero >= 0);
        g
      | old ->
        Log.debug (fun m ->
            m "Tightening %a into %a@." PP.edge old PP.edge e
          );
        unsafe_add_edge { g with graph = B.remove_edge_e g.graph old } e
      | exception Not_found ->
        Log.debug (fun m ->
            m "Adding new edge: %a@." PP.edge e
          );

        unsafe_add_edge g e

  type bound = (W.t * P.t) HM.t

  type bounds = { inf : bound ; sup : bound }

  let get_constant_exn (lb, ub) v =
    match HM.find v lb, HM.find v ub with
    | (inf, _), (sup, _) when W.compare inf sup = 0 -> inf
    | _ | exception Not_found -> raise Not_found

  let is_constant { inf; sup } v =
    match HM.find v inf, HM.find v sup with
    | (inf, _), (sup, _) -> W.compare inf sup = 0
    | exception Not_found -> false

  type bound_ops =
    { get : bounds -> G.V.t -> W.t * P.t
    ; set : bounds -> G.V.t -> W.t -> P.t -> bounds }

  let lower_bound notify =
    let get { inf; _ } v = HM.find_and_raise v inf "get" in
    let set { inf; sup } v w p =
      match HM.find v sup with
      | sup, sup_p when W.compare w sup > 0 ->
        (* p is a path from 0 to v proving w <= v
           sup_p is a path from v to 0 proving v <= sup
           the concatenation is a negative cycle starting in [0] *)
        raise (Negative_cycle (P.append p sup_p))
      | _ | exception Not_found ->
        notify v;
        { inf = HM.add v (w, p) inf ; sup }
    in
    { get ; set }

  let upper_bound notify =
    let get { sup; _ } v = HM.find_and_raise v sup "get" in
    let set { inf; sup } v w p =
      match HM.find v inf with
      | inf, inf_p when W.compare w inf < 0 ->
        (* p is a path from v to 0 proving v <= w
           inf_p is a path from 0 to v proving inf <= v
           the concatenation is a negative cycle starting in [0] *)
        raise (Negative_cycle (P.append inf_p p))
      | _ | exception Not_found ->
        notify v;
        { inf ; sup = HM.add v (w, p) sup }
    in
    { get ; set }

  (* To improve the lower bound on [y], we need to find a path from [0] to [y]
      that is shorter than the current edge [0 - y <= -min y].

      We know that the old lower bounds [omin] satisfy the fact that the path
      from [0] to [y] of length [-omin y] is the shortest path from [0] to [y].
      For any node [x], if there is a path of length [k] from [x] to [y], the
      path from [0] to [y] that goes through [x] has length [-omin x + k].
      Hence, we have:

      [-omin y <= -omin x + sp(x, y)]

      where [sp(x, y)] is the shortest path from [x] to [y] in the original
      graph.

      Some of the lower bounds have been increased, so that the above property
      no longer holds for [min]; this is the property we want to restore. We
      also allow the above property to be broken for [omin] on the vertices [y]
      for which [min] and [omin] differs; this allows to add new constraints to
      the graph. *)
  let tighten_ops gops g bops b changed =
    (* This is [potential 0]

        For any vertex [v] whose bound has been updated we have:

        potential 0 - min v - potential v >= 0

        We only need to take into consideration the bounds that have been
        updated because we will never consider paths that go through an edge
        from [0] to a node whose bounds have not been updated. *)
    let acc = ref None in
    S.iter (fun v ->
        let inf, _ = bops.get b v in
        let minv' = inf + gops.potential g v in
        match !acc with
        | Some ground ->
          if W.compare minv' ground > 0 then acc := Some minv'
        | None ->
          acc := Some minv'
      ) changed;
    let ground =
      match !acc with
      | Some acc -> acc
      | None ->
        (* Any value works here, we will not do anything *)
        W.zero
    in

    let visited = Vtbl.create 97 in
    (* [distance v] is the length of the shortest path so far from 0 to v
        in the reduced cost graph *)
    let distance = Vtbl.create 97 in
    let pq = H.create 97 in

    let rec loop g b =
      match H.pop_min pq with
      | exception Not_found -> g, b
      | elt ->
        let s = elt.target in
        if Vtbl.mem visited s then
          loop g b
        else (
          Vtbl.replace visited s ();

          (* [elt.weight] is the reduced cost of the shortest path that starts
              with an updated bound from 0 to s.

              [weight elt + potential s - ground] is the weight of that path in
              the original graph, which induces a new lower bound [new_min] for
              [s] (the lower bound is the negation of the length). *)
          let new_min_s = ground - elt.weight - gops.potential g s in

          (* If the new bound does not improve on the old bound, we do not
              need to consider further paths that go through [s], otherwise
              that would translate to an improvement of an old bound, which are
              already tight wrt the graph. *)
          if
            S.mem s changed ||
            W.compare new_min_s (fst @@ bops.get b s) > 0
          then (
            let potential_s = elt.weight + gops.potential g s in
            gops.iter_succ_e (fun edge ->
                let t = G.E.dst edge in
                if not (Vtbl.mem visited t) then (
                  let dt = potential_s + weight edge - gops.potential g t in
                  let improved =
                    try W.compare dt (Vtbl.find distance t) < 0
                    with Not_found -> true
                  in
                  if improved then (
                    Vtbl.replace distance t dt;
                    H.insert pq
                      { target = t
                      ; weight = dt
                      ; path = gops.append elt.path (path edge) }
                  )
                )
              ) g.graph s;

            let b = bops.set b s new_min_s elt.path in
            let g =
              if is_constant b s then
                { g with graph = B.remove_vertex g.graph s }
              else
                g
            in
            loop g b
          ) else
            loop g b
        )
    in

    S.iter (fun v ->
        let inf, path = bops.get b v in
        let distance_v = ground - inf + gops.potential g v in
        Vtbl.replace distance v distance_v;
        H.insert pq
          { target = v
          ; weight = distance_v
          ; path = path }
      ) changed;
    loop g b

  let tighten_inf ~notify g b changed =
    tighten_ops forward_ops g (lower_bound notify) b changed

  let tighten_sup ~notify g b changed =
    tighten_ops backward_ops g (upper_bound notify) b changed

  type t =
    { graph : g
    ; bounds : bounds
    ; inf_changed : S.t R.t
    ; sup_changed : S.t R.t }

  let pp : t Fmt.t = fun _ppf _t -> ()

  let solve_exn { graph; bounds; inf_changed; sup_changed } =
    let inf_improved = ref S.empty in
    let notify_inf v = inf_improved := S.add v !inf_improved in
    let graph, bounds =
      if not (S.is_empty (R.get inf_changed)) then
        tighten_inf ~notify:notify_inf graph bounds (R.get inf_changed)
      else
        graph, bounds
    in
    let sup_improved = ref S.empty in
    let notify_sup v = sup_improved := S.add v !sup_improved in
    let graph, bounds =
      if not (S.is_empty (R.get sup_changed)) then
        tighten_sup ~notify:notify_sup graph bounds (R.get sup_changed)
      else
        graph, bounds
    in
    { inf_improved = !inf_improved ; sup_improved = !sup_improved },
    { graph
    ; bounds
    ; inf_changed = R.create S.empty
    ; sup_changed = R.create S.empty }

  let add_lower_bound bounds inf_changed x k p =
    match HM.find x bounds.inf with
    | inf, _ when W.compare inf k > 0 ->
      (bounds, inf_changed)
    | _ | exception Not_found ->
      let bounds = (lower_bound ignore).set bounds x k p in
      (bounds, (R.set inf_changed (S.add x (R.get inf_changed))))

  let add_upper_bound bounds sup_changed x k p =
    match HM.find x bounds.sup with
    | sup, _ when W.compare sup k < 0 ->
      (bounds, sup_changed)
    | _ | exception Not_found ->
      let b = (upper_bound ignore).set bounds x k p in
      (b, (R.set sup_changed (S.add x (R.get sup_changed))))

  let lower_bound_exn { bounds; _ } x =
    HM.find x bounds.inf

  let upper_bound_exn { bounds; _ } x =
    HM.find x bounds.sup

  let add_edge_e { graph; bounds; inf_changed; sup_changed } e =
    (* First update the bounds, then add the edge.

       If either end is known to be constant, we don't need to actually add the
       edge: bounds propagation is sufficient since it is closed under
       transitive paths. *)

    let x = G.E.src e and k = weight e and y = G.E.dst e in
    let bounds, inf_changed =
      match HM.find x bounds.inf with
      | (inf, inf_p) ->
        (* x - y <= k /\ 0 - x <= -inf -> 0 - y <= -(inf - k) *)
        add_lower_bound
          bounds inf_changed y (inf - k) (P.append inf_p (path e))
      | exception Not_found ->
        bounds, inf_changed
    in
    let bounds, sup_changed =
      match HM.find y bounds.sup with
      | (sup, sup_p) ->
        (* x - y <= k /\ y - 0 <= sup -> x - 0 <= sup + k *)
        add_upper_bound
          bounds sup_changed x (sup + k) (P.append (path e) sup_p)
      | exception Not_found ->
        bounds, sup_changed
    in
    if not (is_constant bounds x || is_constant bounds y) then
      { graph = add_edge_e graph e ; bounds ; inf_changed ; sup_changed }
    else
      { graph ; bounds ; inf_changed ; sup_changed }

  let add_lower_bound t x k p =
    let bounds, inf_changed = add_lower_bound t.bounds t.inf_changed x k p in
    { t with bounds; inf_changed }

  let add_upper_bound t x k p =
    let bounds, sup_changed = add_upper_bound t.bounds t.sup_changed x k p in
    { t with bounds; sup_changed }

  let add_delta_le t x y k p =
    add_edge_e t (G.E.create x (k, p) y)

  let add_delta_eq t x y k p =
    (* Make sure we need to restore potential at most once *)
    if W.compare (potential t.graph x + k - potential t.graph y) W.zero < 0 then
      let t = add_delta_le t y x (-k) p in
      add_delta_le t x y k p
    else
      let t = add_delta_le t x y k p in
      add_delta_le t y x (-k) p
end

module Sig = struct
  module type S = sig
    type t

    type vertex

    type weight

    type path
    (** A path represents a series of {b true} difference constraints.

        Consecutive elements in the path share a variable that can be
        eliminated, so that a path

          x1 - x2 <= k1 ; x2 - x3 <= k2 ; x3 - x4 <= k3

        justifies the inequality

          x1 - x4 <= k1 + k2 + k3 *)

    val lower_bound_exn : t -> vertex -> weight * path
    (** @raise Not_found if [x] has no lower bound. *)

    val upper_bound_exn : t -> vertex -> weight * path
    (** @raise Not_found if [x] has no upper bound. *)

    module S : Set.S

    type improvement = { inf_improved : S.t ; sup_improved : S.t }
    (** This type is used by [solve_exn] to indicate variables whose lower/upper
        bounds have been improved during solving. *)
  end

  module type P = sig
    include S

    val empty : t
    (** Empty solver with no constraints. *)

    val add_lower_bound : t -> vertex -> weight -> path -> t
    (** [add_upper_bound t x k p] adds the constraint [k <= x]. [p] is a path
        that justifies adding this constraint.

        {b Note}: This function delays actual propagation of the constraint
        until the next call to [solve].

        @raises Negative_cycle if [k] is higher than [x]'s upper bound. *)

    val add_upper_bound : t -> vertex -> weight -> path -> t
    (** [add_upper_bound t x k p] adds the constraint [x <= k]. [p] is a path
        that justifies adding this constraint.

        {b Note}: This function delays actual propagation of the constraint
        until the next call to [solve].

        @raises Negative_cycle if [k] is smaller than [x]'s lower bound. *)

    val add_delta_le : t -> vertex -> vertex -> weight -> path -> t
    (** [add_delta_eq t x y k p] adds the constraint [x - y <= k]. [p] is a path
        that justifies adding this constraint.

        @raises Negative_cycle if a negative cycle is found while processing the
        constraint. *)

    val add_delta_eq : t -> vertex -> vertex -> weight -> path -> t
    (** [add_delta_eq t x y k p] adds the constraint [x - y = k]. [p] is a path
        that justifies adding this constraint.

        [add_delta_eq] is logically equivalent to calling [add_delta_le] twice,
        but it is guaranteed to do perform at most one graph traversal and can
        be more efficient.

        @raises Negative_cycle if a negative cycle is found while processing the
        constraint. *)

    val solve_exn : t -> improvement * t
    (** If the system has a solution, returns a pair [improvement, t] where
        [improvement] contains information about the bounds that have been
        tightened since the last call to [solve].

        It is possible that [improvement] includes bounds that were updated
        through [add_lower_bound] or [add_upper_bound] but were not changed by
        [solve].

        If the system has no solution, raises a [Negative_cycle] exception. The
        path in the negative cycle is guaranteed to start and end on [0]. *)
  end
end

module type VERTEX = sig
  include Graph.Sig.COMPARABLE

  val pp : t Fmt.t
end

module Make(V : VERTEX)(P : PATH) = struct
  module E = struct
    type t = Z.t * P.t

    let compare (x, _) (y, _) = Z.compare x y

    let default = Z.zero, P.empty
  end

  module Persistent = struct
    module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(V)(E)

    module B = Graph.Builder.P(G)

    module HM = Graph.Blocks.Make_Map(V)

    module R = struct
      type 'a t = 'a

      let create x = x

      let get x = x

      let set _ x = x
    end

    module S = Set.Make(V)

    module PP = struct
      let vertex = V.pp

      let edge ppf (x, (z, _), y) =
        Fmt.pf ppf "%a -{%a}-> %a"
          V.pp x Z.pp_print z V.pp y
    end

    module M = Impl (Z)(P)(B)(S)(HM)(R)(PP)

    exception Negative_cycle = M.Negative_cycle

    type t = M.t

    let pp = M.pp

    let empty =
      let graph = B.empty () in
      let potentials = HM.empty in
      let bounds = M.{ inf = HM.empty ; sup = HM.empty } in
      let inf_changed = S.empty in
      let sup_changed = S.empty in
      M.{ graph = { graph ; potentials } ; bounds ; inf_changed ; sup_changed }

    let solve_exn = M.solve_exn

    let lower_bound_exn = M.lower_bound_exn

    let add_lower_bound = M.add_lower_bound

    let upper_bound_exn = M.upper_bound_exn

    let add_upper_bound = M.add_upper_bound

    let add_delta_le = M.add_delta_le

    let add_delta_eq = M.add_delta_eq
  end

  module Imperative = struct
    module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(V)(E)

    module B = Graph.Builder.I(G)

    module HM = Graph.Blocks.Make_Hashtbl(V)

    module R = struct
      type 'a t = 'a ref

      let create x = ref x

      let get x = !x

      let set x v = x := v; x
    end

    module S = Set.Make(V)

    module PP = struct
      let vertex = V.pp

      let edge ppf (x, (z, _), y) =
        Fmt.pf ppf "%a -{%a}-> %a"
          V.pp x Z.pp_print z V.pp y
    end

    module M = Impl (Z)(P)(B)(S)(HM)(R)(PP)

    let create ?size () =
      let graph = B.empty () in
      let potentials = HM.create ?size () in
      let bounds = M.{ inf = HM.create ?size () ; sup = HM.create ?size () } in
      let inf_changed = ref S.empty in
      let sup_changed = ref S.empty in
      M.{ graph = { graph ; potentials } ; bounds ; inf_changed ; sup_changed }

    let solve_exn t =
      let improvement, _ = M.solve_exn t in
      improvement

    let lower_bound_exn = M.lower_bound_exn

    let add_lower_bound t x k p =
      ignore (M.add_lower_bound t x k p)

    let upper_bound_exn = M.upper_bound_exn

    let add_upper_bound t x k p =
      ignore (M.add_upper_bound t x k p)

    let add_delta_le t x y k p =
      ignore (M.add_delta_le t x y k p)

    let add_delta_eq t x y k p =
      ignore (M.add_delta_eq t x y k p)
  end
end

module Path_explanation = struct
  type t = Explanation.t

  let empty = Explanation.empty

  let append = Explanation.union
end

module E = Make(struct include Expr let pp = print end)(Path_explanation)
module X = Make(struct
    type t = Shostak.Combine.r

    let hash = Shostak.Combine.hash

    let equal = Shostak.Combine.equal

    let compare = Shostak.Combine.str_cmp

    let pp = Shostak.Combine.print
  end)(Path_explanation)
