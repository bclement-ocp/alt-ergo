(** The store that the union-find data structure lives in.

    Using [Store.Historical] enables backtracking support through
    [Store.Historical.Snapshot] and [Store.Historical.Atomic]. *)
type -'a store = 'a Store.Historical.t

(** An equivalence class of ['a] values that have been merged. An equivalence
    class is always non-empty and has a distinguished member called its
    representative. *)
type 'a class'

val croot : 'a class' -> 'a option

(** Iterate over the values in the equivalence class. *)
val iter : ('a -> unit) -> 'a class' -> unit

(** Fold over the values in the equivalence class. *)
val fold : ('a -> 'b -> 'a) -> 'a -> 'b class' -> 'a

(** A cell contains union-find metadata associated with a value.

    Note that this module does not prevent you from creating multiple cells
    associated with the same value. It is the user's responsibility to prevent
    this (e.g. using a hash table or through other mechanisms) if required. *)
type ('a, 'b) cell

(** [cell s v] creates a new cell with value [v].

    It is guaranteed that [v] is in the equivalence class of the resulting cell
    in all stores. *)
val cell : ?term:'b -> 'a -> ('a, 'b) cell

(** [class' s c] returns the class associated with cell [c] in the store [s].

    If [c] was created with initial value [v], it is guaranteed that [v] is a
    member of the [class' s c] for *any* store [s]. *)
val class' : [> `R ] store -> ('a, 'b) cell -> 'b class'

val value : [> `R ] store -> ('a, 'b) cell -> 'a

(** [union store x y ex] adds the equality [x = y] in the store [store], with
    justification [ex].

    If [cmp] is provided, the minimum value of [repr x] and [repr y] is used as
    a new representative. *)
val union :
  ?cmp:('a -> 'a -> int) ->
  [> `R | `W ] store -> ('a, 'b) cell -> ('a, 'b) cell -> Explanation.t ->
  ('a -> 'a -> int) ->
  Explanation.t

(** [find store cell] returns a triple [r, c, ex] where:

    - [r] is the representative value of cell [cell]
    - [c] is the equivalence class of all terms equal to [r]
    - [ex] is a justification for the equality between the original value of
       [cell] and the representative [r] *)
val find : [> `R ]  store -> ('a, 'b) cell -> 'a * 'b class' * Explanation.t

(** [root store cell] returns a pair [rcell, ex] where [rcell] is the
    representative of [cell] and [ex] is a justification for the equality
    between [cell] and [rcell].

    If [cell] is already a representative, then [rcell] is [cell] and [ex] is
    empty. *)
val root : [> `R ] store -> ('a, 'b) cell -> ('a, 'b) cell * Explanation.t
