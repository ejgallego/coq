Require Import Program.

Program Definition foo (X : Type) : Type :=
  let x := X in forall x : x, _.

Next Obligation.
refine nat.
Defined.
