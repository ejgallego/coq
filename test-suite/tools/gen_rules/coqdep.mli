module Vodep : sig
  type t =
    { target : string
    ; deps : string list
    }
end

type dep = | VO of Vodep.t | MLG of string

val parse_coqdep_line : string -> (string list * dep) option
