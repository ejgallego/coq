(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module State : sig
  type t
  val loadpath : t -> Loadpath.State.t
end

(** Type of input files (after they are treated) *)
type vAccu = (string * string) list

(** [init args] Init coqdep, setting arguments from [args]. *)
val init : make_separator_hack:bool -> Args.t -> State.t * vAccu * string list

(** [treat_file_command_line file] Add an input file to be considered  *)
val treat_file_command_line : vAccu -> string -> vAccu

val compute_deps :
  meta_files:string list ->
  vAccu ->
  State.t -> Dep_info.t list

val canonize : vAccu -> string -> string
