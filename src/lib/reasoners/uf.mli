(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

(** {1 Uf module} *)

type t

type eclass

exception Inconsistent of Explanation.t * eclass list

type r = Shostak.Combine.r

module LX : Xliteral.S with type elt = r

val empty : unit -> t
val add : t -> Expr.t -> t * Expr.t list

val mem : t -> Expr.t -> bool

val find : t -> Expr.t -> r * Explanation.t

val find_r : t -> r -> r * Explanation.t

val union :
  t -> r -> r -> Explanation.t ->
  t * (r * (r * r * Explanation.t) list * r) list

val distinct : t -> r list -> Explanation.t -> t

val are_equal : t -> Expr.t -> Expr.t -> added_terms:bool -> (Explanation.t * eclass list) option
val are_distinct : t -> Expr.t -> Expr.t -> (Explanation.t * eclass list) option
val already_distinct : t -> r list -> bool

val class_of : t -> Expr.t -> Expr.t list

val fold_rclass_of : t -> (Expr.t -> 'a -> 'a) -> r -> 'a -> 'a

val cl_extract : t -> eclass list

val print : t -> unit
val print_tagged_classes : eclass list Fmt.t
val term_repr : t -> Expr.t -> Expr.t

val make : t -> Expr.t -> r (* may raise Not_found *)

val is_normalized : t -> r -> bool

val assign_next : t -> (r Xliteral.view * bool) list * t

(** {2 Counterexample function} *)

(** Compute a counterexample using the Uf environment and then print it on the
    given formatter with the corresponding format setted with
    Options.get_output_format *)
val output_concrete_model :
  Format.formatter ->
  prop_model:Expr.Set.t ->
  t ->
  unit

(** saves the module's cache *)
val save_cache : unit -> unit

(** reinitializes the module's cache with the saved one *)
val reinit_cache : unit -> unit
