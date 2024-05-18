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
    if false then
      k (Printer.print_dbg ~module_name:"Delta")

  let info k =
    k (Printer.print_dbg ~module_name:"Delta")
end

module type WEIGHT = sig
  type t

  val pp_print : t Fmt.t

  val compare : t -> t -> int

  val add : t -> t -> t

  val zero : t

  val sub : t -> t -> t
end

module WeightNotations(W : WEIGHT) = struct
  let ( + ) = W.add

  let ( - ) = W.sub

  let (~-) = W.sub W.zero
end

module type PATH = sig
  type t

  val empty : t

  val append : t -> t -> t
end

module type OrderedTypeDefault = sig
  type t

  val compare : t -> t -> int

  val default : t
end

module Pqueue(V : OrderedTypeDefault) : sig
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

module Core
    (W : WEIGHT)
    (P : PATH)
    (B : Graph.Builder.S with type G.E.label = W.t * P.t)
    (HM : Graph.Blocks.HM with type key = B.G.V.t)
    (PP : sig val vertex : B.G.V.t Fmt.t val edge : B.G.E.t Fmt.t end) : sig
  type g =
    { graph : B.G.t
    ; potentials : W.t HM.t }

  type graph_ops =
    { potential : g -> B.G.V.t -> W.t
    ; iter_succ_e : (B.G.E.t -> unit) -> B.G.t -> B.G.V.t -> unit
    ; src : B.G.E.t -> B.G.V.t
    ; dst : B.G.E.t -> B.G.V.t
    ; append : P.t -> P.t -> P.t }

  val forward_ops : graph_ops

  val backward_ops : graph_ops

  val remove_vertex : g -> B.G.V.t -> g

  val reduced_cost : g -> B.G.E.t -> W.t

  val add_edge_e : g -> B.G.E.t -> g

  val subst : g -> B.G.V.t -> B.G.V.t -> W.t -> P.t -> g

  module Vtbl : Hashtbl.S with type key = B.G.V.t

  module Elt : sig
    type t = { target : B.G.V.t ; weight : W.t ; path : P.t }

    val compare : t -> t -> int

    val default : t
  end

  module H : module type of Pqueue(Elt)

  val weight : B.G.E.t -> W.t

  val path : B.G.E.t -> P.t

  exception Negative_cycle of P.t
end =
struct
  open WeightNotations(W)

  module G = B.G

  type g =
    { graph : G.t
    ; potentials : W.t HM.t }

  let remove_vertex g v =
    { graph = B.remove_vertex g.graph v
    ; potentials = HM.remove v g.potentials }

  let potential' p v =
    try HM.find v p with Not_found -> W.zero

  let potential g v = potential' g.potentials v

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

  (* Precondition: All edges other than [e] have a nonnegative reduced cost.
     Precondition: [e] has a negative reduced cost.

     Postcondition: All edges have a nonnegative reduced cost. *)
  let compute_new_potential g e =
    let x = G.E.src e and y = G.E.dst e in

    (* Vertices for which the negative shortest path has been found. *)
    let visited = Vtbl.create 97 in

    (* [distance t] is the length of the shortest {b negative} path from [x] to
       [t] that starts with [edge] and only goes through [visited] vertices.

       If [t] is in [visited], this is the actual negative shortest path from
       [x] to [t]. *)
    let distance = Vtbl.create 97 in

    (* Min-queue of candidate nodes. *)
    let pq = H.create 97 in

    let rec loop () =
      match H.pop_min pq with
      | exception Not_found ->
        (* We have found all negative shortest paths from [x]. *)
        ()
      | elt ->
        let s = elt.target in
        if Vtbl.mem visited s then loop () else (
          (* w is [wSP(x, s) < 0] *)
          let w = elt.weight in
          assert (W.compare w W.zero < 0);
          if G.V.equal s x then
            (* There is a path from [x] to itself with negative weight: the
               path proves [x - x < 0].

               Note that since [e] is the only negative edge in the reduced
               graph, any negative cycle starting in [x] necessarily comes back
               to [x]. *)
            raise (Negative_cycle elt.path)
          else (
            Vtbl.replace visited s ();

            (* Fix the negative slack for s then propagate forward *)
            let new_potential_s = potential g s + w in
            G.iter_succ_e (fun edge ->
                let t = G.E.dst edge in
                if not (Vtbl.mem visited t) then (
                  (* The shortest path in the reduced graph from [x] to [s] has
                     (negative) length [w].

                     For any edge [e] from [s] to [t] with weight [k], it
                     induces a path in the reduced graph from [x] to [t] with
                     length [dt = w + potential s + k - potential t]. *)
                  let dt = new_potential_s + weight edge - potential g t in
                  let improved =
                    (* Note: only keep negative paths. *)
                    try W.compare dt (Vtbl.find distance t) < 0
                    with Not_found -> W.compare dt W.zero < 0
                  in
                  if improved then (
                    (* Best negative path from [x] to [t] so far. *)
                    Vtbl.replace distance t dt;
                    H.insert pq
                      { weight = dt
                      ; target = t
                      ; path = P.append elt.path (path edge) }
                  )
                )
              ) g.graph s;

            loop ()
          )
        )
    in

    (* Base case: the shortest negative path (barring cycles) from [x] to [y] is
       just the edge [e]. *)
    let dy = reduced_cost g e in
    assert (W.compare dy W.zero < 0);
    Vtbl.replace distance y dy;
    H.insert pq
      { weight = dy
      ; target = y
      ; path = path e };

    loop ();

    (* Compute a new potential for [s] as [potential s + min(wSP(x, s), 0)]
       where [wSP(x, s)] is the length of the shortest path from [x] to [s].

       All edges in the graph have a nonnegative reduced cost with this new
       potential:

       - For the edge [x - y <= k] that had a negative reduced cost, we have
         [wSP(x, y) = potential x + k - potential y] hence:
          [new_potential x + k - new_potential y = 0]

         (recall that [wSP(x, x) = 0] since we don't have any negative cycles).

       - If [wSP(x, s) >= 0], then [new_potential s = potential s] and for any
         edge [s - t <= k] we have [potential s + k - potential t >= 0] hence
         [new_potential s + k - new_potential t >= 0] (because the new potential
         for [t] is always smaller than the old potential for [t]).

       - If [wSP(x, s) < 0], then [new_potential s = potential s + wSP(x, s)]
         and for any edge [s - t <= k], there is a path from [x] to [t] going
         through that edge, hence:

          [wSP(x, t) <= wSP(x, s) + potential s + k - potential t]

         which yields [new_potential s + k - new_potential t >= 0] since
         [new_potential t <= potential t + wSP(x, t)]. *)
    Vtbl.fold (fun v slack new_potential ->
        assert (W.compare slack W.zero < 0);
        HM.add v (potential g v + slack) new_potential
      ) distance g.potentials

  (* Precondition: All edges other than [e] have a nonnegative reduced cost.

     Postcondition: All edges have a nonnegative reduced cost. *)
  let restore_potential g e =
    if W.compare (reduced_cost g e) W.zero < 0 then
      { g with potentials = compute_new_potential g e }
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
      (* Make sure to have at most one edge between [x] and [y]. *)
      match G.find_edge g.graph x y with
      | old when W.compare (weight old) (weight e) <= 0 ->
        (* We already have a tighter constraint *)
        assert (W.compare (reduced_cost g e) W.zero >= 0);
        g
      | old ->
        Log.debug (fun m ->
            m "Tightening %a into %a@." PP.edge old PP.edge e
          );
        let graph = B.remove_edge_e g.graph old in
        restore_potential { g with graph = B.add_edge_e graph e } e
      | exception Not_found ->
        Log.debug (fun m ->
            m "Adding new edge: %a@." PP.edge e
          );

        restore_potential { g with graph = B.add_edge_e g.graph e } e

  (* rr = nrr + k *)
  let subst g rr nrr k p_rr_nrr =
    let g =
      G.fold_succ_e (fun e g ->
          (* rr <= dst + w_rr_dst -> nrr <= dst + (w_rr_dst - k) *)
          let dst = G.E.dst e in
          let (w_rr_dst, p_rr_dst) = G.E.label e in
          add_edge_e g @@
          G.E.create nrr (W.sub w_rr_dst k, P.append p_rr_nrr p_rr_dst) dst
        ) g.graph rr g
    in
    let g =
      G.fold_pred_e (fun e g ->
          (* src <= rr + w_src_rr -> src <= nrr + (w_src_rr + k) *)
          let src = G.E.src e in
          let (w_src_rr, p_src_rr) = G.E.label e in
          add_edge_e g @@
          G.E.create src (W.add w_src_rr k, P.append p_src_rr p_rr_nrr) nrr
        ) g.graph rr g
    in
    remove_vertex g rr

  type graph_ops =
    { potential : g -> G.V.t -> W.t
    ; iter_succ_e : (G.E.t -> unit) -> G.t -> G.V.t -> unit
    ; src : G.E.t -> G.V.t
    ; dst : G.E.t -> G.V.t
    ; append : P.t -> P.t -> P.t }

  let wrap_iter iter f g v =
    if G.mem_vertex g v then iter f g v

  let forward_ops =
    { src = G.E.src
    ; dst = G.E.dst
    ; iter_succ_e = wrap_iter G.iter_succ_e
    ; potential = potential
    ; append = P.append }

  let backward_ops =
    { src = G.E.dst
    ; dst = G.E.src
    ; iter_succ_e = wrap_iter G.iter_pred_e
    ; potential = (fun g v -> -potential g v)
    ; append = (fun p q -> P.append q p) }
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
  include Core(W)(P)(B)(HM)(PP)

  module G = B.G

  open WeightNotations(W)

  type bound = (W.t * P.t) HM.t

  type bounds = { inf : bound ; sup : bound }

  type bound_ops =
    { get : bounds -> G.V.t -> W.t * P.t
    ; set : bounds -> G.V.t -> W.t -> P.t -> bounds }

  (* Given a graph [(g, b, changed)] that satisfy partial transitivity,
     [tighten_ops] tightens the bound [b'] such that the graph [(g, b, empty)]
     satisfies partial transitivity (i.e. [(g, b)] satisfies total
     transitivity).

     In other words:

      For any {b unchanged} vertex [v], the shortest path from [0] to [v]
      {b that only goes through unchanged vertices} has length [-min v].

     Becomes:

      For any vertex [v], the shortest path from [0] to [v] has length [-min v].

     Let us assume that [v] is an unchanged vertex such that the shortest path
     from [0] to [v] has length [sp(0, v) < spu(0, v)] where [spu(0, v)] is the
     shortest path from [0] to [v] with only unchanged vertices.

     There is necessarily a changed vertex [w] in this shortest path, otherwise
     it would be the shortest unchanged path. The shortest path from [0] to [w]
     followed by the shortest path from [w] to [v] is then a valid path from [0]
     to [v], which is necessarily the shortest.

     Hence, it is only necessary to consider the paths that {b start} by an edge
     from [0] to a changed vertex. *)
  let tighten_ops gops g bops b changed =
    (* Compute [ground] as a virtual [potential 0].

       We ensure that [ground - min v - potential v >= 0] holds for {b changed}
       vertices only. *)
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
        in the reduced cost graph (recall that only paths starting with a
        changed vertex are considered). *)
    let distance = Vtbl.create 97 in
    let pq = H.create 97 in

    let rec loop b =
      match H.pop_min pq with
      | exception Not_found -> b
      | elt ->
        let s = elt.target in
        if Vtbl.mem visited s then
          loop b
        else (
          Vtbl.replace visited s ();

          (* [elt.weight] is the reduced cost of the shortest path from 0 to s
             starting with a changed vertex.

             [weight elt + potential s - ground] is the weight of that path in
             the original graph, which induces a new lower bound [new_min] for
             [s] (the lower bound is the negation of the length). *)
          let new_min_s = ground - elt.weight - gops.potential g s in

          (* If [s] is a changed vertex, we always need to consider further
             paths going through [s]: any path going through [s] goes through a
             changed vertex.

             If [s] is an unchanged vertex and the lower bound does not improve,
             we do not need to consider further paths going through [s]. If
             there is a new shortest path from [0] to [t] going through [s],
             there must be a changed vertex [v] on the path from [s] to [t] (the
             shortest path from [0] to [s] is also the shortest unchanged path).
             The first such changed vertex [v] is such that the path from [0] to
             [v] going through [s] cannot improve on the edge from [0] to [v] of
             length [-min v]. *)
          if
            S.mem s changed ||
            (match fst @@ bops.get b s with
             | lb -> W.compare new_min_s lb > 0
             | exception Not_found -> true)
          then (
            let potential_s = elt.weight + gops.potential g s in
            gops.iter_succ_e (fun edge ->
                let t = gops.dst edge in
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

            loop (bops.set b s new_min_s elt.path)
          ) else
            loop b
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
    loop b

  let set_lower_bound ~notify bounds v w p =
    match HM.find v bounds.sup with
    | sup, sup_p when W.compare w sup > 0 ->
      (* p is a path from 0 to v proving w <= v
          sup_p is a path from v to 0 proving v <= sup
          the concatenation is a negative cycle starting in [0] *)
      raise (Negative_cycle (P.append p sup_p))
    | _ | exception Not_found ->
      notify v;
      { bounds with inf = HM.add v (w, p) bounds.inf }

  let set_upper_bound ~notify bounds v w p =
    match HM.find v bounds.inf with
    | inf, inf_p when W.compare w inf < 0 ->
      (* p is a path from v to 0 proving v <= w
          inf_p is a path from 0 to v proving inf <= v
          the concatenation is a negative cycle starting in [0] *)
      raise (Negative_cycle (P.append inf_p p))
    | _ | exception Not_found ->
      notify v;
      { bounds with sup = HM.add v (w, p) bounds.sup }

  let tighten_inf ~notify g b changed =
    let get { inf; _ } v = HM.find v inf
    and set = set_lower_bound ~notify in
    tighten_ops forward_ops g { get; set } b changed

  let tighten_sup ~notify g b changed =
    let get { sup; _ } v =
      let (w, p) = HM.find v sup in
      (-w, p)
    and set bounds v w p = set_upper_bound ~notify bounds v (-w) p in
    tighten_ops backward_ops g { get; set } b changed

  type t =
    { graph : g
    ; bounds : bounds
    ; inf_changed : S.t R.t
    ; sup_changed : S.t R.t }
  (* We maintain the following invariants for [inf] (the same invariants hold
     for [sup] in the mirror graph):

     - We say that a vertex [x] has changed if it is in [inf_changed] and is
        unchanged otherwise.

     - The shortest path from [0] to an {b unchanged} vertex [x] that only goes
        through unchanged vertices has length [-min x] (in particular, the edge
        from [0] to [x] in [bounds] is such a path).

     - The shortest path from [0] to a {b changed} vertex [x] that only goes
        through unchanged vertices (except for [x]), if it exists, is longer
        than [-min x].

     If [x] and [y] are unchanged vertices, and there is a path of length [k]
     from [x] to [y] that only goes through unchanged vertices, it induces a
     path of length [-min x + k] from [0] to [y] hence we have:

      [-min y <= -min x + k]

     In particular, [-min y <= -min x + sp(x, y)] where [sp(x, y)] is the length
     of the shortest {b unchanged} path from [x] to [y].

     Adding a new edge from [x] to [y] of length [k] might break this invariant
     if it induces a path from [0] to some unchanged vertex [z] of shorter
     length than [-min z].

     This new path must use the edge from [x] to [y]. We must have a path from
     [0] to [x], then a path from [x] to [y], then a path from [y] to [z].

     This is only possible if the path from [0] to [y] that goes through [x] is
     shorter than the existing path from [0] to [y].

     Hence, this is only possible if [y] becomes changed.

     Hence, this new path would go through the changed vertex [y].

     Hence, we do not break the invariant. *)

  let pp_lower_bound ppf (v, (lb, _ex)) =
    Fmt.pf ppf "%a <= %a" W.pp_print lb PP.vertex v

  let pp_upper_bound ppf (v, (lb, _ex)) =
    Fmt.pf ppf "%a <= %a" PP.vertex v W.pp_print lb

  let pp : t Fmt.t = fun ppf t ->
    let needs_cut = ref false in
    let cut_if_needed () =
      if !needs_cut then Fmt.cut ppf ();
      needs_cut := true
    in

    if not (G.is_empty t.graph.graph) then (
      cut_if_needed ();
      Fmt.iter ~sep:Fmt.cut G.iter_edges_e (Fmt.box PP.edge) ppf t.graph.graph
    );

    if not (HM.is_empty t.bounds.inf) then (
      cut_if_needed ();
      Fmt.iter_bindings ~sep:Fmt.cut HM.iter (Fmt.box pp_lower_bound)
        ppf t.bounds.inf
    );

    if not (HM.is_empty t.bounds.sup) then (
      cut_if_needed ();
      Fmt.iter_bindings ~sep:Fmt.cut HM.iter (Fmt.box pp_upper_bound)
        ppf t.bounds.sup
    );

    if not (HM.is_empty t.graph.potentials) then (
      cut_if_needed ();
      Fmt.pf ppf "=== POTENTIALS ===@,";
      Fmt.iter_bindings ~sep:Fmt.cut HM.iter
        (Fmt.box @@ Fmt.pair ~sep:(Fmt.any " =@ ") PP.vertex W.pp_print)
        ppf t.graph.potentials
    )

  let pp = Fmt.vbox pp

  type improvement = { inf_improved : S.t ; sup_improved : S.t }

  let is_constant { inf; sup } v =
    match HM.find v inf, HM.find v sup with
    | (inf, _), (sup, _) -> W.compare inf sup = 0
    | exception Not_found -> false

  let solve_exn { graph; bounds; inf_changed; sup_changed } =
    let inf_changed = R.get inf_changed and sup_changed = R.get sup_changed in
    let inf_improved = ref S.empty in
    let notify_inf v = inf_improved := S.add v !inf_improved in
    let bounds =
      if not (S.is_empty inf_changed) then
        tighten_inf ~notify:notify_inf graph bounds inf_changed
      else
        bounds
    in
    let sup_improved = ref S.empty in
    let notify_sup v = sup_improved := S.add v !sup_improved in
    let bounds =
      if not (S.is_empty sup_changed) then
        tighten_sup ~notify:notify_sup graph bounds sup_changed
      else
        bounds
    in
    let remove_if_constant v (graph : g) =
      if is_constant bounds v then
        remove_vertex graph v
      else
        graph
    in
    let graph =
      S.fold remove_if_constant sup_changed @@
      S.fold remove_if_constant inf_changed @@
      graph
    in
    { inf_improved = !inf_improved ; sup_improved = !sup_improved },
    { graph
    ; bounds
    ; inf_changed = R.create S.empty
    ; sup_changed = R.create S.empty }

  let add_lower_bound bounds inf_changed x k p =
    match HM.find x bounds.inf with
    | inf, _ when W.compare inf k >= 0 ->
      (bounds, inf_changed)
    | _ | exception Not_found ->
      Log.debug (fun m ->
          m "Improving lower bound: %a <= %a@."
            W.pp_print k PP.vertex x
        );
      let bounds = set_lower_bound ~notify:ignore bounds x k p in
      (bounds, (R.set inf_changed (S.add x (R.get inf_changed))))

  let add_upper_bound bounds sup_changed x k p =
    match HM.find x bounds.sup with
    | sup, _ when W.compare sup k <= 0 ->
      (bounds, sup_changed)
    | _ | exception Not_found ->
      Log.debug (fun m ->
          m "Improving upper bound: %a <= %a@."
            PP.vertex x W.pp_print k
        );
      let b = set_upper_bound ~notify:ignore bounds x k p in
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
      (* If the lower bound for [y] has changed, we need to to inf prop? *)
      (* If the upper bound for [x] has changed, we need to to sup prop? *)
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
    let e = G.E.create x (k, p) y in
    let rev_e = G.E.create y (-k, p) x in
    (* Make sure we need to restore potential at most once *)
    if
      W.compare (reduced_cost t.graph e) W.zero < 0
    then
      let t = add_edge_e t rev_e in
      add_edge_e t e
    else
      let t = add_edge_e t e in
      add_edge_e t rev_e

  (* rr = nrr + k *)
  let subst t rr nrr k p =
    assert (not (G.V.equal rr nrr));
    let t = add_delta_eq t rr nrr k p in
    let t =
      match lower_bound_exn t rr with
      | lb, p_lb_x ->
        (* lb <= x <-> lb <= y + k <-> lb - k <= y *)
        add_lower_bound t nrr (W.sub lb k) (P.append p_lb_x p)
      | exception Not_found -> t
    in
    let t =
      match upper_bound_exn t rr with
      | ub, p_x_ub ->
        (* x <= ub <-> y + k <= ub <-> y <= ub - k *)
        add_upper_bound t nrr (W.sub ub k) (P.append p p_x_ub)
      | exception Not_found -> t
    in
    let bounds =
      { inf = HM.remove rr t.bounds.inf ; sup = HM.remove rr t.bounds.sup }
    in
    let inf_changed =
      R.set t.inf_changed (S.add nrr @@ S.remove rr @@ R.get t.inf_changed)
    in
    let sup_changed =
      R.set t.sup_changed (S.add nrr @@ S.remove rr @@ R.get t.sup_changed)
    in
    let graph = subst t.graph rr nrr k p in
    { graph ; bounds ; inf_changed ; sup_changed }
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

          [x1 - x2 <= k1 ; x2 - x3 <= k2 ; x3 - x4 <= k3]

        from [x1] to [x4] justifies the inequality

          [x1 - x4 <= k1 + k2 + k3] *)

    val lower_bound_exn : t -> vertex -> weight * path
    (** [lower_bound_exn t v] returns a pair [(w, p)] where [w] is the current
        lower bound for [v] and [p] is a path from [0] to [v] of length [w].

        @raise Not_found if [v] has no lower bound. *)

    val upper_bound_exn : t -> vertex -> weight * path
    (** [upper_bound_exn t v] returns a pair [(w, p)] where [w] is the current
        upper bound for [v] and [p] is a path from [v] to [0] of length [w].

        @raise Not_found if [v] has no upper bound. *)

    module S : Set.S with type elt = vertex

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
        but it is guaranteed to perform at most one graph traversal and can
        be more efficient.

        @raises Negative_cycle if a negative cycle is found while processing the
        constraint. *)

    val subst : t -> vertex -> vertex -> weight -> path -> t
    (** [subst t x y k p] {b replaces} the vertex [x] with [y + k]. [p] is a
        path that justifies the equality [x - y = k].

        [subst] is similar to [add_delta_eq], except that [x] is removed from
        the graph entirely: any constraint [z - x <= k'] is replaced with a new
        constraint [z - y <= k' + k], and any constraint [x - z <= k'] is
        replaced with a new constraint [y - z <= k' - k].

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
        Fmt.pf ppf "%a - %a <= %a"
          V.pp x V.pp y Z.pp_print z
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

    let subst = M.subst
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
