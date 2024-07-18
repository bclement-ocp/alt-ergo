(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2024 --- OCamlPro SAS                                *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

(**
   This module implements a global solver for difference constraints, i.e.
   constraints of the form {m x - y \leq d} where {m x} and {m y} are variables
   and {m d} is an integer constraint.

   The implementation of draws heavily from the description of Feydy, Schutt and
   Stuckey [1], in particular regarding the separate handling of bounds
   constraints. This documentation, however, intends to be self-documenting and
   no reference to the paper should be needed.

   [1]: Global difference constraint propagation for finite domain solvers.
    Feydy, T., Schutt, A. & Stuckey, P. (2008).
    PPDP'08 - Proceedings of the 10th International ACM SIGPLAN Symposium on
    Principles and Practice of Declarative Programming, pp. 226-235.
    doi:10.1145/1389449.1389478
*)

type level =
  | App
  | Error
  | Warning
  | Info
  | Debug

let level =
  match try Sys.getenv "AE_VERBOSE" with Not_found -> "" with
  | "app" -> App
  | "error" -> Error
  | "warning" -> Warning
  | "info" -> Info
  | "debug" -> Debug
  | _ -> Error

module Log = struct
  let msg l k =
    if Stdlib.(l <= level) then
      k (Printer.print_dbg ~module_name:"Delta")

  let app k = msg App k

  let err k = msg Error k

  let warn k = msg Warning k

  let debug k = msg Debug k

  let info k = msg Info k
end

(** {2 Interfaces} *)

(** Module signature for constant value types, used as the right-hand side of a
    difference constraint {m x - y <= d}. *)
module type VALUE = sig
  type t
  (** The type of values. *)

  val pp_print : t Fmt.t
  (** Pretty-printer for values.

      {b Note}: We use the name [pp_print] here rather than [pp] because we
      expect the [Z] moduel from Zarith to be used as values in most
      situations. *)

  val compare : t -> t -> int
  (** Comparison function for values. *)

  val add : t -> t -> t
  (** Addition. Must be associative and commutative. *)

  val zero : t
  (** Neutral element for addition: [add x zero = x] for all [x]. *)

  val sub : t -> t -> t
  (** Subtraction. Must have [sub x y = z] iff [add z y = x]. *)
end

(** Module signature for oriented and ordered justifications. *)
module type PATH = sig
  type t
  (** The type of paths. Conceptually, a path represents a sequence of
      (justifications of) difference constraints that can simplify: consecutive
      elements in a path must share a variable that can be eliminated.

      For instance, a path:

        [x1 - x2 <= k1 ; x2 - x3 <= k2 ; x3 - x4 <= k3]

      from [x1] to [x4] justifies the inequality:

        [x1 - x4 <= k1 + k2 + k3]. *)

  val pp : t Fmt.t
  (** Pretty-printer for paths. *)

  val empty : t
  (** The empty path. *)

  val append : t -> t -> t
  (** [append p1 p2] constructs a path [p] from [p1] and [p2].

      The last variable of [p1] must be equal to the first variable of [p2],
      otherwise the behavior of this function is unspecified. *)
end

(** Module signature for variables, used in the left-hand side of difference
    constraints. *)
module type VARIABLE = sig
  type t
  (** The type of variables. *)

  val pp : t Fmt.t
  (** Pretty-printer for variables. *)

  val equal : t -> t -> bool
  (** Equality on variables. *)

  val compare : t -> t -> int
  (** Comparison of variables. *)

  val hash : t -> int
  (** Hash function on variables. *)

  val default : t
  (** Default variable, used as a placeholder. Can be any value of the proper
      type.*)

  type value
  (** The type of values that the variables can take. This is used for the
      [lower_bound_exn] and [upper_bound_exn] functions below. *)

  val lower_bound_exn : t -> value
  (** Returns the intrinsic lower bound of this variable, if any.

      {b Note}: The returned lower bound must be valid in all contexts.

      @raises Not_found if the variable is unbounded below. *)

  val upper_bound_exn : t -> value
  (** Returns the intrinsic upper bound of with this variable, if any.

      {b Note}: The returned upper bound must be valid in all contexts.

      @raises Not_found if the variable is unbounded above. *)
end

(** {2 Implementation} *)

module Make(W : VALUE)(V : VARIABLE with type value = W.t)(P : PATH) : sig
  type t
  (** The type of global difference constraints. *)

  val pp : t Fmt.t
  (** Pretty-printer for global difference constraints. *)

  val empty : t
  (** The empty global constraint. *)

  exception Negative_cycle of P.t
  (** Exception raised by the various [*_exn] functions below when an
      inconsistency is detected.

      Internally, difference constraints are represented as edges in a weighted
      graph. An inconsistency corresponds to a negative cycle, i.e. a path
      proving [x - x < 0] for some variable [x]. *)

  (** {2 Accessing information} *)

  val mem : t -> V.t -> bool
  (** [mem t x] returns [true] iff there is a constraint associated with [x] in
      [t]. *)

  val lower_bound_exn : t -> V.t -> W.t * P.t
  (** [lower_bound_exn t v] returns the lower bound associated with variable [v]
      and its justification.

      @raises Not_found if [v] is unbounded below. *)

  val upper_bound_exn : t -> V.t -> W.t * P.t
  (** [upper_bound_exn t v] returns the upper bound associated with variable [v]
      and its justification.

      @raises Not_found if [v] is unbounded above. *)

  (** {2 Constraints} *)

  val add_lower_bound_exn : t -> V.t -> W.t -> P.t -> t
  (** [add_lower_bound_exn t x k p] registers a lower bound [k <= x] justified
      by [p], which must be a path from [0] to [x].

      {b Note}: The resulting problem is not guaranteed to be satisfiable, even
      if no exception is raised. See {!is_sat} and {!solve_exn}.

      @raises Negative_cycle if the upper bound for [x] is less than [k]. *)

  val add_upper_bound_exn : t -> V.t -> W.t -> P.t -> t
  (** [add_lower_bound_exn t x k p] registers an upper bound [x <= k] justified
      by [p], which must be a path from [x] to [0].

      {b Note}: The resulting problem is not guaranteed to be satisfiable, even
      if no exception is raised. See {!is_sat} and {!solve_exn}.

      @raises Negative_cycle if the lower bound for [x] is greater than [k]. *)

  val add_constraint_exn : t -> V.t -> V.t -> W.t -> P.t -> t
  (** [add_constraint_exn t x y k p] registers the difference constraint
      [x - y <= k] with justification [p], which must be a path from [x] to [y].

      {b Note}: The resulting problem is not guaranteed to be satisfiable, even
      if no exception is raised. See {!is_sat} and {!solve_exn}.

      @raises Negative_cycle if a negative cycle is found while processing the
      constraint. *)

  (** {2 Substitution} *)

  val assign_exn : t -> V.t -> W.t -> P.t -> t
  (** [assign_exn t x k p] performs the destructive assignment [x := k] with
      justification [p] (i.e. [p] justifies that [x = k] holds).

      The variable [x] no longer appears in the resulting problem.

      {b Note}: The resulting problem is not guaranteed to be satisfiable, even
      if no exception is raised. See {!is_sat} and {!solve_exn}.

      @raises Negative_cycle if an inconsistency is detected while performing
        the assignment. *)

  val subst_exn : t -> V.t -> V.t -> W.t -> P.t -> t
  (** [subst_exn t x y k p] performs the substitution [x := y + k] with
      justification [p] (i.e. [p] justifies that [x - y = k] holds).

      The variable [x] no longer appears in the resulting problem.

      {b Note}: The resulting problem is not guaranteed to be satisfiable, even
      if no exception is raised. See {!is_sat} and {!solve_exn}.

      @raises Negative_cycle if an inconsistency is detected while performing
        the assignment. *)

  (** {2 Solving} *)

  val is_sat : t -> bool
  (** Returns [true] if propagation is needed to ensure consistency.

      If [false], the current environment is already solved and calling [solve]
      will do nothing. *)

  val solve_exn : ?notify:(V.t -> unit) -> t -> t
  (** Solve the current problem and returns a solution if it exists.

      If provided, the [notify] function is used to notify the caller when the
      bounds for a variable has changed since the last call to [solve_exn]. Note
      that the changed bounds are not included in the notification; if needed,
      they should be read from the returned solution (if satisfiable).

      {b Note}: Notifications will be emitted for bound changes resulting from
      calls to [add_lower_bound] and [add_upper_bound] since the last call to
      [solve], even if this call to [solve] does not refine those bounds
      further.

      If it does not raise, [solve_exn] is guaranteed to return a satisfiable
      environment, and is guaranteed to return the given environment unmodified
      if [is_sat] returns [true].

      @raises Negative_cycle if the environment is unsatisfiable. *)
end =
struct
  module G = Graph.Persistent.Digraph.ConcreteBidirectionalLabeled(V)(struct
      type t = W.t * P.t

      let compare (x, _) (y, _) = W.compare x y

      let default = W.zero, P.empty
    end)
  module B = Graph.Builder.P(G)

  module MV = Map.Make(V)
  module SV = Set.Make(V)

  (* Handy notations *)
  let ( + ) = W.add
  let ( - ) = W.sub
  let (~-) = W.sub W.zero

  type t =
    { graph : G.t
    (** The graph of difference constraints between variables.

        An edge from [u] to [v] is labelled with a pair [(w, p)] where [w] is
        a weight and [p] is a path, and represents the constraint:
          [p => u - v <= w]
        that is understood to be true in the current context.

        In addition to the vertices explicitly represented in the graph, we
        assume the existence of a virtual vertex, denoted [0], to represent
        constant values; see the [inf] and [inf_changed] fields. *)

    ; potential : W.t MV.t
    (** Map from vertices in the graph to their current potential. Missing
        entries are treated as zero.

        We do not keep track of a potential for the virtual node [0]; when
        needed, an appropriate potential is computed from the information in
        [inf] and [sup].

        We maintain the invariant that for any edge [u -{w}-> v] in [g], the
        reduced cost [potential(u) + w - potential(v)] is nonnegative.

        Note that for a cycle, the reduced cost is identical to the weight in
        the original graph since the potentials cancel each other. *)

    ; inf : (W.t * P.t) MV.t
    (** Map from vertices in the graph to their current known infimum and a
        justification for it. Missing entries are unbounded below.

        An entry [v -> (w, p)] in the map represents the constraint:
          [p => w <= v]
        or:
          [p => 0 - v <= -w]

        This can be understood as a virtual edge [0 -{-w, p}-> v] from the
        virtual vertex [0] to [v]. *)

    ; inf_changed : SV.t
    (** Set of vertices whose infimum has changed (improved).

        Let us say that a vertex is {e changed} if it is in [inf_changed], and
        that is it {e unchanged} otherwise. Let us further say that a path is
        {e changed} if it goes through at least one changed vertex (other than
        the start and the end of the path), and that it is {e unchanged}
        otherwise.

        We maintain the invariant that the shortest {b unchanged} path from
        [0] to an {b unchanged} vertex [t] is the virtual edge from [0] to [t]
        with cost [-inf t].

        In particular, if [inf_changed] is empty, the shortest path from [0]
        to [t] has cost [-inf t]. *)

    ; sup : (W.t * P.t) MV.t
    (** Map from vertices in the graph to their current known supremum and a
        justification for it. Missing entries are unbounded above.

        This is equivalent to [inf] in the mirror graph; see the documentation
        for [inf]. *)

    ; sup_changed : SV.t
    (** Set of vertices whose supremum has changed (improved).

        This is equivalent to [inf_changed] in the mirror graph; see the
        documentation for [inf_changed]. *)

    }

  let empty =
    { graph = G.empty
    ; potential = MV.empty
    ; inf = MV.empty
    ; inf_changed = SV.empty
    ; sup = MV.empty
    ; sup_changed = SV.empty
    }

  let weight e = fst @@ G.E.label e

  let path e = snd @@ G.E.label e

  let potential pi v =
    try MV.find v pi with Not_found -> W.zero

  let pp_vertex pi ppf v =
    Fmt.pf ppf "%a [pi = %a]" V.pp v W.pp_print (potential pi v)

  let pp_edge pi ppf e =
    Fmt.pf ppf "@[%a - %a <= %a@ %a@]"
      (pp_vertex pi) (G.E.src e)
      (pp_vertex pi) (G.E.dst e)
      W.pp_print (weight e)
      P.pp (path e)

  let pp_lower_bound changed ppf (v, (lb, _ex)) =
    let star = if SV.mem v changed then "*" else "" in
    Fmt.pf ppf "%a <=%s %a" W.pp_print lb star V.pp v

  let pp_upper_bound changed ppf (v, (lb, _ex)) =
    let star = if SV.mem v changed then "*" else "" in
    Fmt.pf ppf "%a <=%s %a" V.pp v star W.pp_print lb

  let pp ppf { graph ; potential ; inf ; inf_changed ; sup ; sup_changed } =
    let needs_cut = ref false in
    let cut_if_needed () =
      if !needs_cut then Fmt.cut ppf ();
      needs_cut := true
    in

    if not (G.is_empty graph) then (
      cut_if_needed ();
      Fmt.iter ~sep:Fmt.cut G.iter_edges_e (pp_edge potential) ppf graph
    );

    if not (MV.is_empty inf) then (
      cut_if_needed ();
      Fmt.iter_bindings ~sep:Fmt.cut MV.iter
        Fmt.(box (pp_lower_bound inf_changed)) ppf inf;
    );

    if not (MV.is_empty sup) then (
      cut_if_needed ();
      Fmt.iter_bindings ~sep:Fmt.cut MV.iter
        Fmt.(box (pp_upper_bound sup_changed)) ppf sup
    )

  let set_potential pi v w =
    if W.compare w W.zero = 0 then MV.remove v pi
    else MV.add v w pi

  let reduced_cost pi e =
    potential pi (G.E.src e) + weight e - potential pi (G.E.dst e)

  exception Negative_cycle of P.t

  let negative_cycle p = raise_notrace (Negative_cycle p)

  let mem t x =
    G.mem_vertex t.graph x || MV.mem x t.inf || MV.mem x t.sup

  let set_lower_bound_exn ~sup inf x k p =
    match MV.find x sup with
    | sup, sup_p when W.compare k sup > 0 ->
      (* p is a path from 0 to v proving w <= v
          sup_p is a path from v to 0 proving v <= sup
          the concatenation is a negative cycle starting in [0] *)
      negative_cycle (P.append p sup_p)
    | _ | exception Not_found ->
      MV.add x (k, p) inf

  let set_upper_bound_exn ~inf sup v w p =
    match MV.find v inf with
    | inf, inf_p when W.compare w inf < 0 ->
      (* p is a path from v to 0 proving v <= w
          inf_p is a path from 0 to v proving inf <= v
          the concatenation is a negative cycle starting in [0] *)
      negative_cycle (P.append inf_p p)
    | _ | exception Not_found ->
      MV.add v (w, p) sup

  module Elt = struct
    type t = { target : G.V.t ; weight : W.t ; path : P.t }

    let compare x y = W.compare x.weight y.weight

    let default =
      { target = V.default ; weight = W.zero ; path = P.empty }
  end

  module H = Heap.MakeOrdered(Elt)

  module Vtbl = Hashtbl.Make(G.V)

  (* Precondition: All edges in [g] have a nonnegative reduced cost.
     Precondition: [e] has a negative reduced cost.

     Postcondition: All edges in [g] and [e] have a nonnegative reduced cost.

     We perform an incremental variant of Dijkstra's algorithm computing all the
     *negative* shortest paths in the reduced graph of [g + e] starting from
     vertex [x = src e].

     (Note that since all edges in [g] have a nonnegative reduced cost, any
     negative cycle in [g + e] necessarily goes through [x].)

     If we find a negative cycle in the reduced graph, this leads to a negative
     cycle in [g + e], i.e. a proof that [x - x < 0].

     Otherwise, we shift the potential for any node [s] depending on the value
     of [wSP(x, s)] (the weight of the shortest path from [x] to [s]) to yield
     a nonnegative reduced cost in [g + e] (see below). *)
  let restore_potential_exn g pi e =
    let x = G.E.src e and y = G.E.dst e in
    let dy = reduced_cost pi e in
    assert (W.compare dy W.zero < 0);

    (* Vertices for which the negative shortest path has been found. *)
    let visited = Vtbl.create 97 in

    (* [distance t] is the length of the shortest {b negative} path from [x]
       to [t] that starts with [edge] and only goes through [visited]
       vertices.

       If [t] is in [visited], this is the actual negative shortest path from
       [x] to [t]. *)
    let distance = Vtbl.create 97 in

    (* Min-queue of candidate nodes. *)
    let pq = H.create 97 in

    let rec loop () =
      match H.pop_min pq with
      | exception Not_found ->
        (* We have found all negative shortest paths from [x]. *)
        None
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
               graph, any negative cycle starting in [x] necessarily comes
               back to [x]. *)
            Some elt.path
          else (
            Vtbl.replace visited s ();

            (* Fix the negative slack for s then propagate forward *)
            let new_potential_s = potential pi s + w in
            G.iter_succ_e (fun edge ->
                let t = G.E.dst edge in
                if not (Vtbl.mem visited t) then (
                  (* The shortest path in the reduced graph from [x] to [s]
                     has (negative) length [w].

                     For any edge [e] from [s] to [t] with weight [k], it
                     induces a path in the reduced graph from [x] to [t] with
                     length [dt = w + potential s + k - potential t]. *)
                  let dt = new_potential_s + weight edge - potential pi t in
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
              ) g s;

            loop ()
          )
        )
    in

    (* Base case: the shortest negative path (barring cycles) from [x] to [y]
       is just the edge [e]. *)
    Vtbl.replace distance y dy;
    H.insert pq
      { weight = dy
      ; target = y
      ; path = path e };

    match loop () with
    | Some path -> negative_cycle path
    | None ->
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
           [new_potential s + k - new_potential t >= 0] (because the new
           potential for [t] is always smaller than the old potential for [t]).

         - If [wSP(x, s) < 0], then [new_potential s = potential s + wSP(x, s)]
           and for any edge [s - t <= k], there is a path from [x] to [t] going
           through that edge, hence:

            [wSP(x, t) <= wSP(x, s) + potential s + k - potential t]

          which yields [new_potential s + k - new_potential t >= 0] since
          [new_potential t <= potential t + wSP(x, t)]. *)
      Vtbl.fold (fun v slack pi' ->
          assert (W.compare slack W.zero < 0);
          set_potential pi' v (potential pi v + slack)
        ) distance pi

  let find_lower_bound_exn inf x =
    try MV.find x inf with Not_found -> V.lower_bound_exn x, P.empty

  let lower_bound_exn t x = find_lower_bound_exn t.inf x

  let add_lower_bound_exn ({ inf ; sup ; inf_changed ; _ } as t) x k p_0_x =
    match find_lower_bound_exn inf x with
    | inf, _ when W.compare inf k >= 0 -> t
    | _ | exception Not_found ->
      Log.debug (fun m ->
          m "Improving lower bound to: %a <= %a@ "
            W.pp_print k V.pp x);
      let inf = set_lower_bound_exn ~sup inf x k p_0_x in
      let inf_changed = SV.add x inf_changed in
      { t with inf ; inf_changed }

  let find_upper_bound_exn sup x =
    try MV.find x sup with Not_found -> V.upper_bound_exn x, P.empty

  let upper_bound_exn t x = find_upper_bound_exn t.sup x

  let add_upper_bound_exn ({ inf ; sup ; sup_changed ; _ } as t) x k p_x_0 =
    match find_upper_bound_exn sup x with
    | sup, _ when W.compare sup k <= 0 -> t
    | _ | exception Not_found ->
      Log.debug (fun m ->
          m "Improving upper bound: %a <= %a@."
            V.pp x W.pp_print k
        );
      let sup = set_upper_bound_exn ~inf sup x k p_x_0 in
      let sup_changed = SV.add x sup_changed in
      { t with sup ; sup_changed }

  let is_constant { inf ; sup ; _ } x =
    match MV.find x inf, MV.find x sup with
    | (inf, _), (sup, _) -> W.compare inf sup = 0
    | exception Not_found -> false

  let add_edge_exn t e =
    let x = G.E.src e and k = weight e and y = G.E.dst e in
    if G.V.equal x y then
      (* We do not store reflexive edges, but still need to check consistency *)
      if W.compare k W.zero >= 0 then t else negative_cycle (path e)
    else
      let t =
        match MV.find x t.inf with
        | (inf, inf_p) ->
          (* x - y <= k /\ 0 - x <= -inf -> 0 - y <= -(inf - k) *)
          add_lower_bound_exn
            t y (inf - k) (P.append inf_p (path e))
        | exception Not_found -> t
      in
      let t =
        match MV.find y t.sup with
        | (sup, sup_p) ->
          (* x - y <= k /\ y - 0 <= sup -> x - 0 <= sup + k *)
          add_upper_bound_exn
            t x (sup + k) (P.append (path e) sup_p)
        | exception Not_found -> t
      in
      if is_constant t x || is_constant t y then t
      else
      if W.compare (reduced_cost t.potential e) W.zero >= 0 then
        (* Ensure only the tightest constraint is kept. *)
        match G.find_edge t.graph x y with
        | old ->
          if W.compare (weight old) k <= 0 then t
          else
            { t with graph = B.add_edge_e (B.remove_edge_e t.graph old) e }
        | exception Not_found ->
          { t with graph = B.add_edge_e t.graph e }
      else
        (* Restore the broken potentials *)
        let potential = restore_potential_exn t.graph t.potential e in
        let graph = B.add_edge_e (B.remove_edge t.graph x y) e in
        { t with graph ; potential }

  let add_delta_le_exn t x y k p =
    add_edge_exn t (G.E.create x (k, p) y)

  let add_delta_eq_exn t x y k p =
    let e = G.E.create x (k, p) y in
    let rev_e = G.E.create y (-k, p) x in
    (* Make sure we need to restore potential at most once *)
    if W.compare (reduced_cost t.potential e) W.zero < 0
    then
      let t = add_edge_exn t rev_e in
      add_edge_exn t e
    else
      let t = add_edge_exn t e in
      add_edge_exn t rev_e

  let add_constraint_exn t x y k p =
    add_delta_le_exn t x y k p

  (** {2 Substitution} *)

  (* Marked as incomplete because we can in general lose constraints. *)
  let incomplete_remove t x =
    let graph = B.remove_vertex t.graph x in
    let potential = MV.remove x t.potential in
    let inf = MV.remove x t.inf in
    let sup = MV.remove x t.sup in
    let inf_changed = SV.remove x t.inf_changed in
    let sup_changed = SV.remove x t.sup_changed in
    { graph ; potential ; inf ; sup ; inf_changed ; sup_changed }

  (* p_rr_nrr => rr = nrr + k *)
  let subst_exn t rr nrr k p_rr_nrr =
    let t = add_delta_eq_exn t rr nrr k p_rr_nrr in
    let t =
      match lower_bound_exn t rr with
      | lb, p_lb_rr ->
        (* lb <= rr <-> lb <= nrr + k <-> lb - k <= nrr *)
        add_lower_bound_exn t nrr (lb - k) (P.append p_lb_rr p_rr_nrr)
      | exception Not_found -> t
    in
    let t =
      match upper_bound_exn t rr with
      | ub, p_rr_ub ->
        (* rr <= ub <-> nrr + k <= ub <-> nrr <= ub - k *)
        add_upper_bound_exn t nrr (ub - k) (P.append p_rr_nrr p_rr_ub)
      | exception Not_found -> t
    in
    let t =
      if not (G.mem_vertex t.graph rr) then t
      else
        let t =
          G.fold_succ_e (fun e t ->
              (* rr <= dst + w_rr_dst -> nrr <= dst + (w_rr_dst - k) *)
              let dst = G.E.dst e in
              let (w_rr_dst, p_rr_dst) = G.E.label e in
              add_edge_exn t @@
              G.E.create nrr (w_rr_dst - k, P.append p_rr_nrr p_rr_dst) dst
            ) t.graph rr t
        in
        G.fold_pred_e (fun e t ->
            (* src <= rr + w_src_rr -> src <= nrr + (w_src_rr + k) *)
            let src = G.E.src e in
            let (w_src_rr, p_src_rr) = G.E.label e in
            add_edge_exn t @@
            G.E.create src (w_src_rr + k, P.append p_src_rr p_rr_nrr) nrr
          ) t.graph rr t
    in
    (* Consider an arbitrary path [u -*-> u' -{ku}-> rr -{kv}-> v' -*-> v] in
       the graph, where we might have [u = u'] or [v = v'].

       By adding new edges for the successors and predecessors of [rr], we made
       sure that we have an edge [u' -> nrr] with cost at most [ku - k] and
       an edge [nrr -> v'] with cost at most [kv + k]. This entails a path

        [u -*-> u' -> nrr -> v' -*-> v]

       that is also in the graph and never longer.

       Hence, we can remove [rr] from the graph without losing constraints. *)
    incomplete_remove t rr

  let assign_exn t x cte p =
    let () =
      match lower_bound_exn t x with
      | lb, p_0_x when W.compare cte lb < 0 ->
        negative_cycle (P.append p_0_x p)
      | _ | exception Not_found -> ()
    in
    let () =
      match upper_bound_exn t x with
      | ub, p_x_0 when W.compare ub cte < 0 ->
        negative_cycle (P.append p p_x_0)
      | _ | exception Not_found -> ()
    in
    let t =
      if not (G.mem_vertex t.graph x) then t
      else
        let t =
          G.fold_succ_e (fun e t ->
              (* x <= dst + w_rr_dst -> cte - w_rr_dst <= dst *)
              let dst = G.E.dst e in
              let (w_rr_dst, p_rr_dst) = G.E.label e in
              add_lower_bound_exn
                t dst (cte - w_rr_dst) (P.append p p_rr_dst)
            ) t.graph x t
        in
        G.fold_pred_e (fun e t ->
            (* src <= x + w_src_rr -> src <= cte + w_src_rr *)
            let src = G.E.src e in
            let (w_src_rr, p_src_rr) = G.E.label e in
            add_upper_bound_exn
              t src (cte + w_src_rr) (P.append p_src_rr p)
          ) t.graph x t
    in
    (* Consider an arbitrary path [u -*-> u' -{ku}-> x -{kv}-> v' -*-> v] in the
       graph, where we might have [u = u'] or [v = v'].

       By updating the bounds of the predecessors and successors of [x], we
       make sure that we have [sup u' <= ku + cte] and [kv - cte <= inf v'], so
       that the path

         [u -*-> u' -{sup u'}-> 0 -{-inf v'}-> v' -*-> v]

       is also in the graph and never longer.

       Hence, we can remove [x] from the graph without losing constraints. *)
    incomplete_remove t x

  (** {2 Solving} *)

  type 'pi graph_ops =
    { potential : 'pi -> G.V.t -> W.t
    ; iter_succ_e : (G.E.t -> unit) -> G.t -> G.V.t -> unit
    ; src : G.E.t -> G.V.t
    ; dst : G.E.t -> G.V.t
    ; append : P.t -> P.t -> P.t }

  type 'b bound_ops =
    { get_exn : 'b -> G.V.t -> W.t * P.t
    (* Raises [Not_found] if there is no bound. *)
    ; set_exn : 'b -> G.V.t -> W.t -> P.t -> 'b
    (* Raises [Negative_cycle] if the new bound is inconsistent. *)
    }

  (* Given a graph [(g, b, changed)] that satisfy partial transitivity,
     [tighten_ops] tightens the bound [b'] such that the graph [(g, b, empty)]
     satisfies partial transitivity (i.e. [(g, b)] satisfies total
     transitivity).

     In other words:

      For any {b unchanged} vertex [v], the shortest path from [0] to [v]
      {b that only goes through unchanged vertices} has length [-min v].

     Becomes:

      For any vertex [v], the shortest path from [0] to [v] has length [-min v].

     This algorithm is similar to [restore_broken_potential] in that it also
     uses a limited variant of Dijkstra's algorithm, but the limitations are
     different enough that it warrants its own separate implementation. In
     [restore_broken_potential], we are looking for the shortest paths starting
     from a specific vertex [x] with a negative weight. In [tighten_ops], we
     are looking at changed paths (positive or negative) that might improve
     the bounds associated with a vertex.

     Note that the description for [tighten_ops] assumes that we are tightening
     the lower bound in the original graph, but equivalently we could be
     tightening the upper bound in the mirror graph.

     Let us assume that [v] is an unchanged vertex such that the shortest path
     from [0] to [v] has length [sp(0, v) < spu(0, v)] where [spu(0, v)] is the
     shortest path from [0] to [v] with only unchanged vertices.

     There is necessarily a changed vertex [w] in this shortest path, otherwise
     it would be the shortest unchanged path. The shortest path from [0] to [w]
     followed by the shortest path from [w] to [v] is then a valid path from [0]
     to [v], which is necessarily the shortest.

     Hence, it is only necessary to consider the paths that {b start} by an edge
     from [0] to a changed vertex. *)
  let tighten_ops gops g pi bops b changed =
    (* Compute [ground] as a potential for the virtual vertex [0].

       We ensure that [ground - min v - potential v >= 0] holds for {b changed}
       vertices only. *)
    assert (not (SV.is_empty changed));
    let ground =
      match
        SV.fold (fun v ground_opt ->
            match bops.get_exn b v with
            | exception Not_found ->
              (* [v] is in [changed] and hence must have a defined bound. *)
              assert false
            | inf, _ ->
              let minv' = inf + gops.potential pi v in
              match ground_opt with
              | Some ground ->
                if W.compare minv' ground > 0 then Some minv'
                else ground_opt
              | None ->
                Some minv'
          ) changed None
      with
      | Some ground -> ground
      | None ->
        (* [changed] must not be empty *)
        assert false
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
          let new_min_s = ground - elt.weight - gops.potential pi s in

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
            SV.mem s changed ||
            (match fst @@ bops.get_exn b s with
             | lb -> W.compare new_min_s lb > 0
             | exception Not_found -> true)
          then (
            let potential_s = elt.weight + gops.potential pi s in
            gops.iter_succ_e (fun edge ->
                let t = gops.dst edge in
                if not (Vtbl.mem visited t) then (
                  let dt = potential_s + weight edge - gops.potential pi t in
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
              ) g s;

            Log.debug (fun m ->
                m "Improving %a to %a@." V.pp s W.pp_print new_min_s
              );
            loop (bops.set_exn b s new_min_s elt.path)
          ) else
            loop b
        )
    in

    SV.iter (fun v ->
        match bops.get_exn b v with
        | exception Not_found ->
          (* [v] is in [changed] and hence must have a finite bound. *)
          assert false
        | inf, path ->
          let distance_v = ground - inf - gops.potential pi v in
          Vtbl.replace distance v distance_v;
          H.insert pq
            { target = v
            ; weight = distance_v
            ; path = path }
      ) changed;
    loop b

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
    ; potential = (fun pi v -> -potential pi v)
    ; append = (fun p q -> P.append q p) }

  let tighten_inf_exn ~notify ({ inf ; sup ; inf_changed ; _ } as t) =
    if SV.is_empty inf_changed then t
    else
      let get_exn inf v = MV.find v inf
      and set_exn inf v w p =
        let inf = set_lower_bound_exn ~sup inf v w p in
        notify v; inf
      in
      let bops = { get_exn ; set_exn } in
      let inf =
        tighten_ops forward_ops t.graph t.potential bops inf inf_changed
      in
      { t with inf ; inf_changed = SV.empty }

  let tighten_sup_exn ~notify ({ inf ; sup ; sup_changed ; _ } as t) =
    if SV.is_empty sup_changed then t
    else
      let get_exn sup v =
        let (w, p) = MV.find v sup in
        (-w, p)
      and set_exn sup v w p =
        let sup = set_upper_bound_exn ~inf sup v (-w) p in
        notify v; sup
      in
      let bops = { get_exn ; set_exn } in
      let sup =
        tighten_ops backward_ops t.graph t.potential bops sup sup_changed
      in
      { t with sup ; sup_changed = SV.empty }

  let remove_if_constant x t =
    if not (is_constant t x) then t
    else
      (* Note: remove from the graph but not the bounds. *)
      let graph = B.remove_vertex t.graph x in
      let potential = MV.remove x t.potential in
      { t with graph ; potential }

  let is_sat { inf_changed ; sup_changed ; _ } =
    SV.is_empty inf_changed && SV.is_empty sup_changed

  let solve_exn ?(notify = ignore) t =
    let to_check = ref SV.empty in
    let notify v =
      to_check := SV.add v !to_check;
      notify v
    in
    let t = tighten_inf_exn ~notify t in
    let t = tighten_sup_exn ~notify t in
    (* The graph is currently tight, so a path [u -> x -> 0] (resp.
       [0 -> x -> u]) through a constant vertex [x] is never shorter than the
       corresponding path [u -> 0] (resp. [0 -> u]) that does not go through
       [x]. *)
    SV.fold remove_if_constant !to_check t
end
