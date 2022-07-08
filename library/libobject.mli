(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Nametab
open Mod_subst

(** [Libobject] declares persistent objects, given with methods:

   * a caching function specifying how to add the object in the current
     scope;
     If the object wishes to register its visibility in the Nametab,
     it should do so for all possible suffixes.

   * a loading function, specifying what to do when the module
     containing the object is loaded;
     If the object wishes to register its visibility in the Nametab,
     it should do so for all suffixes no shorter than the "int" argument

   * an opening function, specifying what to do when the module
     containing the object is opened (imported);
     If the object wishes to register its visibility in the Nametab,
     it should do so for the suffix of the length the "int" argument

   * a classification function, specifying what to do with the object,
     when the current module (containing the object) is ended;
     The possibilities are:
     Dispose    - the object dies at the end of the module
     Substitute - meaning the object is substitutive and
                  the module name must be updated
     Keep       - the object is not substitutive, but survives module
                  closing
     Anticipate - this is for objects that have to be explicitly
                  managed by the [end_module] function (like Require
                  and Read markers)

     The classification function is also an occasion for a cleanup
     (if this function returns Keep or Substitute of some object, the
     cache method is never called for it)

   * a substitution function, performing the substitution;
     this function should be declared for substitutive objects
     only (see above). NB: the substitution might now be delayed
     instead of happening at module creation, so this function
     should _not_ depend on the current environment

   * a discharge function, that is applied at section closing time to
     collect the data necessary to rebuild the discharged form of the
     non volatile objects

   * a rebuild function, that is applied after section closing to
     rebuild the non volatile content of a section from the data
     collected by the discharge function

  Any type defined as a persistent object must be pure (e.g. no references) and
  marshallable by the OCaml Marshal module (e.g. no closures).

*)

type substitutivity = Dispose | Substitute | Keep | Anticipate

(** Both names are passed to objects: a "semantic" [kernel_name], which
   can be substituted and a "syntactic" [full_path] which can be printed
*)

type object_name = Libnames.full_path * KerName.t

module Open_filter : sig

  type t

  val unfiltered : t

  val make : finite:bool -> string CAst.t list -> t
  (** Anomaly when the list is empty. *)

  module Category : sig

    type t
    val make : string -> t
    (** Anomaly if called more than once for a given string. *)

  end

  val simple_open : ?cat:Category.t -> ('i -> 'a -> unit) ->
    t -> 'i -> 'a -> unit
  (** Combinator for making objects with simple category-based open
      behaviour. When [cat:None], can be opened by Unfiltered, but also
      by Filtered with a negative set. *)

  val in_ : cat:Category.t option -> t -> bool
  (** On [cat:None], returns whether the filter allows opening
      uncategorized objects.

      On [cat:(Some category)], returns whether the filter allows
      opening objects in the given [category]. *)


  val and_ : t -> t -> t option
  (** Returns [None] when the intersection is empty. *)

  val or_ :  t -> t -> t

end

type ('a,'b) object_declaration = {
  object_name : string;
  cache_function : 'b -> unit;
  load_function : int -> 'b -> unit;
  open_function : Open_filter.t -> int -> 'b -> unit;
  classify_function : 'a -> substitutivity;
  subst_function :  substitution * 'a -> 'a;
  discharge_function : 'a -> 'a option;
  rebuild_function : 'a -> 'a;
}

(** The default object is a "Keep" object with empty methods.
   Object creators are advised to use the construction
   [{(default_object "MY_OBJECT") with
      cache_function = ...
   }]
   and specify only these functions which are not empty/meaningless

*)

val default_object : string -> ('a,'b) object_declaration

(** the identity substitution function *)
val ident_subst_function : substitution * 'a -> 'a

(** {6 ... } *)
(** Given an object declaration, the function [declare_object_full]
   will hand back two functions, the "injection" and "projection"
   functions for dynamically typed library-objects. *)

(** Common metadata for objects that are stored in modules / .vo files *)
module Data : sig

  type t

  val make : ?loc:Loc.t -> ?doc:string -> ?name:Id.t -> unit -> t

end

(** Behavior specification for a module object; maybe we could use
   OCaml's row-typing here *)
module Behavior : sig

  module Kernel : sig

    (** Objects that update the kernel enviroment. *)
    type t

    (** At some point this will be take a safe_transformer *)
    val make : global:(unit -> unit) -> unit
  end

  module Nametab : sig
    type t
    val make : unit -> unit
  end

  module Summary : sig
    type t
    val with_ref : unit -> t
    val with_map : unit -> t
  end

  type t

  val with_nametab : unit -> t
  val with_summary : Summary.t -> t

end

module Dyn : Dyn.S

type obj = Dyn.t

(** EJGA: Should we attach info to all objects? *)
type algebraic_objects =
  | Objs of t list
  | Ref of ModPath.t * Mod_subst.substitution

and t =
  | ModuleObject of Data.t * substitutive_objects
  (** Information and contents for a Coq Module *)
  | ModuleTypeObject of substitutive_objects
  (** Similar but for module types *)
  | IncludeObject of algebraic_objects
  (** Similar but for include *)
  | KeepObject of t list
  (** A Keep Object is stored at module closing time after the
     [ModuleObject] proper, and with the goal to register the objects
     that survive the module with the [Declaremods] registration
     table. Some other checks are also done. *)
  | ExportObject of { mpl : (Open_filter.t * ModPath.t) list }
  (** [ExportObject] stores a list of objects that must be opened in
     the local context *)
  | AtomicObject of Data.t * Behavior.t * obj
  (** Regular  *)

and substitutive_objects = MBId.t list * algebraic_objects

(** Object declaration and names: if you need the current prefix
   (typically to interact with the nametab), you need to have it
   passed to you.

    - [declare_object_full] and [declare_named_object_gen] pass the
   raw prefix which you can manipulate as you wish.

    - [declare_named_object_full] and [declare_named_object] provide
   the convenience of packaging it with the provided [Id.t] into a
   [object_name].

    - [declare_object] ignores the prefix for you. *)

val declare_object :
  ('a,'a) object_declaration -> ('a -> obj)

val declare_object_full :
  ('a,object_prefix * 'a) object_declaration -> 'a Dyn.tag

val declare_named_object_full :
  ('a,object_name * 'a) object_declaration -> (Id.t * 'a) Dyn.tag

val declare_named_object :
  ('a,object_name * 'a) object_declaration -> (Id.t -> 'a -> obj)

val declare_named_object_gen :
  ('a,object_prefix * 'a) object_declaration -> ('a -> obj)

val cache_object : object_prefix * obj -> unit
val load_object : int -> object_prefix * obj -> unit
val open_object : Open_filter.t -> int -> object_prefix * obj -> unit
val subst_object : substitution * obj -> obj
val classify_object : obj -> substitutivity
val discharge_object : obj -> obj option
val rebuild_object : obj -> obj

(** Higher-level API for objects with fixed scope.

- Local means that the object cannot be imported from outside.
- Global means that it can be imported (by importing the module that contains the
object).
- Superglobal means that the object survives to closing a module, and is imported
when the file which contains it is Required (even without Import).
- With the nodischarge variants, the object does not survive section closing.
  With the normal variants, it does.

We recommend to avoid declaring superglobal objects and using the nodischarge
variants.
*)

val local_object : string ->
  cache:('a -> unit) ->
  discharge:('a -> 'a option) ->
  ('a,'a) object_declaration

val local_object_nodischarge : string ->
  cache:('a -> unit) ->
  ('a,'a) object_declaration

val global_object : ?cat:Open_filter.Category.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  discharge:('a -> 'a option) ->
  ('a,'a) object_declaration

val global_object_nodischarge : ?cat:Open_filter.Category.t -> string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  ('a,'a) object_declaration

val superglobal_object : string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  discharge:('a -> 'a option) ->
  ('a,'a) object_declaration

val superglobal_object_nodischarge : string ->
  cache:('a -> unit) ->
  subst:(Mod_subst.substitution * 'a -> 'a) option ->
  ('a,'a) object_declaration

(** {6 Debug} *)

val dump : unit -> (int * string) list
