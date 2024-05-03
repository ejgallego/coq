(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** To move  *)
val get_extension : string -> string list -> string * string

(* Loadpaths *)
type basename = string
type dirname = string
type filename = string
type dirpath = string list
type root = filename * dirpath

type result =
  | ExactMatches of filename list
  | PartialMatchesInSameRoot of root * filename list

module State : sig
  type t

  val make : unit -> t
end

val search : State.t -> ?from:dirpath -> dirpath -> result option

val add_current_dir : State.t -> System.unix_path -> unit
val add_q_include : State.t -> System.unix_path -> string -> unit
val add_r_include : State.t -> System.unix_path -> string -> unit

(** Only in no boot mode *)
val add_dir_coqlib : State.t -> implicit:bool -> dirname -> dirpath -> unit

val is_in_coqlib : State.t -> ?from:dirpath -> dirpath -> bool

(** [find_dir_logpath phys_dir] Return the logical path of directory
   [dir] if it has been given one. Raise [Not_found] otherwise. In
   particular we can check if "." has been attributed a logical path
   after processing all options and silently give the default one if
   it hasn't. We may also use this to warn if ap hysical path is met
   twice.*)
val find_dir_logpath : string -> string list

(* Used only in "canonize" *)
val absolute_dir : string -> string
val absolute_file_name : filename_concat:(string -> string -> string) -> string -> string option -> string
