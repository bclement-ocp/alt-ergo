(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

include Sig_rel.RELATION

module BV2Nat : sig
  include Uf.GlobalDomain

  val record_int_bounds : Shostak.Combine.r -> Intervals.Int.t -> t -> t
  (** Record bounds for an integer variable and propagate to the corresponding
      bit-vector literal, if any. Must call [flush] afterwards. *)

  val flush : t -> (Shostak.Combine.r Xliteral.view * Explanation.t) list * t
  (** Flushes and returns all pending literals. *)
end

(**/**)

module Test : sig
  val shared_msb : int -> Z.t -> Z.t -> int
end
