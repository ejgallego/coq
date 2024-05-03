(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [find_dependencies] Find the dependencies of a file *)
val find_dependencies
  : canonize:(string -> string)
  -> meta_files:string list
  -> Loadpath.State.t
  -> string                     (** file to analyze *)
  -> Dep_info.Dep.t list

(** [sort] Output full chain of .v dependencies. *)
val sort
  : canonize:(string -> string)
  -> Loadpath.State.t
  -> string list
  -> unit
