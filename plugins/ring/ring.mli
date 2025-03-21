(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr
open Constrexpr
open Ring_ast

val protect_tac_in : string -> Id.t -> unit Proofview.tactic

val protect_tac : string -> unit Proofview.tactic

val add_theory :
  Id.t ->
  constr_expr ->
  constr_expr ring_mod list -> unit

val print_rings : unit -> unit

val ring_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic

val add_field_theory :
  Id.t ->
  constr_expr ->
  constr_expr field_mod list -> unit

val print_fields : unit -> unit

val field_lookup :
  Geninterp.Val.t ->
  constr list ->
  constr list -> constr -> unit Proofview.tactic
