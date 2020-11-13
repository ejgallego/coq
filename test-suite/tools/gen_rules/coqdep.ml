module Vodep = struct
  type t =
    { target : string
    ; deps : string list
    }
end

type dep = | VO of Vodep.t | MLG of string

(* Filter `.vio` etc... *)
let filter_no_vo =
  List.filter (fun f -> Filename.check_suffix f ".vo")

(* This will be removed when we drop support for Make *)
let fix_cmo_cma file =
  if String.equal Filename.(extension file) ".cmo"
  then Util.replace_ext ~file ~newext:".cma"
  else file

(* Process .vfiles.d and generate a skeleton for the dune file *)
let parse_coqdep_line l =
  match Str.(split (regexp ":") l) with
  | [targets;deps] ->
    let targets = Str.(split (regexp "[ \t]+") targets) in
    let deps    = Str.(split (regexp "[ \t]+") deps)    in
    let targets = filter_no_vo targets in
    begin match targets with
    | [target] ->
      let dir, target = Filename.(dirname target, basename target) in
      (* coqdep outputs with the '/' directory separator regardless of
         the platform. Anyways, I hope we can link to coqdep instead
         of having to parse its output soon, that should solve this
         kind of issues *)
      let deps = List.map fix_cmo_cma deps in
      Some (String.split_on_char '/' dir, VO { Vodep.target; deps; })
    (* Otherwise a vio file, we ignore *)
    | _ -> None
    end
  (* Strange rule, we ignore *)
  | _ -> None
