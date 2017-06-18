(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Glob_term

(** Equalities *)

val cases_pattern_eq : cases_pattern -> cases_pattern -> bool

val cast_type_eq : ('a -> 'a -> bool) ->
  'a Misctypes.cast_type -> 'a Misctypes.cast_type -> bool

val glob_constr_eq : glob_constr -> glob_constr -> bool

(** Operations on [glob_constr] *)

val cases_pattern_loc : cases_pattern -> Loc.t option

val cases_predicate_names : tomatch_tuples -> Name.t list

(** Apply one argument to a glob_constr *)
val mkGApp : ?loc:Loc.t -> glob_constr -> glob_constr -> glob_constr

val map_glob_constr :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

(** Ensure traversal from left to right *)
val map_glob_constr_left_to_right :
  (glob_constr -> glob_constr) -> glob_constr -> glob_constr

val warn_variable_collision : ?loc:Loc.t -> Id.t -> unit

val mk_glob_constr_eq : (glob_constr -> glob_constr -> bool) ->
  glob_constr -> glob_constr -> bool

val fold_glob_constr : ('a -> glob_constr -> 'a) -> 'a -> glob_constr -> 'a
val fold_glob_constr_with_binders : (Id.t -> 'a -> 'a) -> ('a -> 'b -> glob_constr -> 'b) -> 'a -> 'b -> glob_constr -> 'b
val iter_glob_constr : (glob_constr -> unit) -> glob_constr -> unit
val occur_glob_constr : Id.t -> glob_constr -> bool
val free_glob_vars : glob_constr -> Id.t list
val bound_glob_vars : glob_constr -> Id.Set.t
(* Obsolete *)
val loc_of_glob_constr : glob_constr -> Loc.t option
val glob_visible_short_qualid : glob_constr -> Id.t list

(* Renaming free variables using a renaming map; fails with
   [UnsoundRenaming] if applying the renaming would introduce
   collision, as in, e.g., renaming [P x y] using substitution [(x,y)];
   inner alpha-conversion done only for forall, fun, let but
   not for cases and fix *)

exception UnsoundRenaming
val rename_var : (Id.t * Id.t) list -> Id.t -> Id.t
val rename_glob_vars : (Id.t * Id.t) list -> glob_constr -> glob_constr

(** [map_pattern_binders f m c] applies [f] to all the binding names
    in a pattern-matching expression ({!Glob_term.GCases}) represented
    here by its relevant components [m] and [c]. It is used to
    interpret Ltac-bound names both in pretyping and printing of
    terms. *)
val map_pattern_binders : (name -> name) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** [map_pattern f m c] applies [f] to the return predicate and the
    right-hand side of a pattern-matching expression
    ({!Glob_term.GCases}) represented here by its relevant components
    [m] and [c]. *)
val map_pattern : (glob_constr -> glob_constr) ->
  tomatch_tuples -> cases_clauses -> (tomatch_tuples*cases_clauses)

(** Conversion from glob_constr to cases pattern, if possible

    Take the current alias as parameter,
    @raise Not_found if translation is impossible *)
val cases_pattern_of_glob_constr : Name.t -> glob_constr -> cases_pattern

val glob_constr_of_closed_cases_pattern : cases_pattern -> Name.t * glob_constr

val add_patterns_for_params_remove_local_defs : constructor -> cases_pattern list -> cases_pattern list

(** {5 Maps of pattern variables} *)

(** Type [constr_under_binders] is for representing the term resulting
    of a matching. Matching can return terms defined in a some context
    of named binders; in the context, variable names are ordered by
    (<) and referred to by index in the term Thanks to the canonical
    ordering, a matching problem like

    [match ... with [(fun x y => ?p,fun y x => ?p)] => [forall x y => p]]

    will be accepted. Thanks to the reference by index, a matching
    problem like

    [match ... with [(fun x => ?p)] => [forall x => p]]

    will work even if [x] is also the name of an existing goal
    variable.

    Note: we do not keep types in the signature. Besides simplicity,
    the main reason is that it would force to close the signature over
    binders that occur only in the types of effective binders but not
    in the term itself (e.g. for a term [f x] with [f:A -> True] and
    [x:A]).

    On the opposite side, by not keeping the types, we loose
    opportunity to propagate type informations which otherwise would
    not be inferable, as e.g. when matching [forall x, x = 0] with
    pattern [forall x, ?h = 0] and using the solution "x|-h:=x" in
    expression [forall x, h = x] where nothing tells how the type of x
    could be inferred. We also loose the ability of typing ltac
    variables before calling the right-hand-side of ltac matching clauses. *)

type constr_under_binders = Id.t list * EConstr.constr

(** Types of substitutions with or w/o bound variables *)

type patvar_map = EConstr.constr Id.Map.t
type extended_patvar_map = constr_under_binders Id.Map.t

(** {5 Closed Globalized Terms} *)

(** A globalised term together with a closure representing the value
    of its free variables. Intended for use when these variables are taken
    from the Ltac environment. *)
type closure = {
  idents  : Id.t Id.Map.t;
  typed   : constr_under_binders Id.Map.t ;
  untyped : closed_glob_constr Id.Map.t }
and closed_glob_constr = {
  closure : closure;
  term    : glob_constr }

(** Ltac variable maps *)
type var_map = constr_under_binders Id.Map.t
type uconstr_var_map = closed_glob_constr Id.Map.t
type unbound_ltac_var_map = Geninterp.Val.t Id.Map.t

type ltac_var_map = {
  ltac_constrs : var_map;
  (** Ltac variables bound to constrs *)
  ltac_uconstrs : uconstr_var_map;
  (** Ltac variables bound to untyped constrs *)
  ltac_idents: Id.t Id.Map.t;
  (** Ltac variables bound to identifiers *)
  ltac_genargs : unbound_ltac_var_map;
  (** Ltac variables bound to other kinds of arguments *)
}

val ltac_interp_name : ltac_var_map -> Names.name -> Names.name
val empty_lvar : ltac_var_map

