(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* gen_rules: generate dune build rules for Coq's test-suite            *)
(* It is desirable that this file can be bootstrapped alone             *)

open Format
open Util

module Options = struct

  type flag = {
    enabled : bool;
    cmd : string;
  }

  let all_opts =
  [ { enabled = false; cmd = "-debug"; }
  ; { enabled = false; cmd = "-native_compiler"; }
  ; { enabled = true; cmd = "-w +default"; }
  ]

  let build_coq_flags () =
    let popt o = if o.enabled then Some o.cmd else None in
    String.concat " " @@ pmap popt all_opts
end

type ddir = Coqdep.dep list DirMap.t

(* We could have coqdep to output dune files directly *)

let gen_sub n =
  (* Move to List.init once we can depend on OCaml >= 4.06.0 *)
  bpath @@ Legacy.list_init n (fun _ -> "..")

let pp_rule fmt targets deps action =
  (* Special printing of the first rule *)
  let ppl = pp_list pp_print_string sep in
  let pp_deps fmt l = match l with
    | [] ->
      ()
    | x :: xs ->
      fprintf fmt "(:pp-file %s)%a" x sep ();
      pp_list pp_print_string sep fmt xs
  in
  fprintf fmt
    "@[(rule@\n @[(targets @[%a@])@\n(deps @[%a@])@\n(action @[%a@])@])@]@\n"
    ppl targets pp_deps deps pp_print_string action

let gen_coqc_targets vo =
  let open Coqdep.Vodep in
  [ vo.target
  ; replace_ext ~file:vo.target ~newext:".glob"
  ; replace_ext ~file:vo.target ~newext:".vos"
  ; "." ^ replace_ext ~file:vo.target ~newext:".aux"]

(* Generate the dune rule: *)
let pp_vo_dep dir fmt vo =
  let open Coqdep.Vodep in
  let depth = List.length dir in
  let sdir = gen_sub depth in
  (* All files except those in Init implicitly depend on the Prelude, we account for it here. *)
  let eflag, edep = if List.tl dir = ["Init"] then "-noinit -R theories Coq", [] else "", [bpath ["theories";"Init";"Prelude.vo"]] in
  (* Coq flags *)
  let cflag = Options.build_coq_flags () in
  (* Correct path from global to local "theories/Init/Decimal.vo" -> "../../theories/Init/Decimal.vo" *)
  let deps = List.map (fun s -> bpath [sdir;s]) (edep @ vo.deps) in
  (* The source file is also corrected as we will call coqtop from the top dir *)
  let source = bpath (dir @ [replace_ext ~file:vo.target ~newext:".v"]) in
  (* We explicitly include the location of coqlib to avoid tricky issues with coqlib location *)
  let libflag = "-coqlib %{project_root}" in
  (* The final build rule *)
  let action = sprintf "(chdir %%{project_root} (run coqc -q %s %s %s %s))" libflag eflag cflag source in
  let all_targets = gen_coqc_targets vo in
  pp_rule fmt all_targets deps action

let pp_mlg_dep _dir fmt ml =
  fprintf fmt "@[(coq.pp (modules %s))@]@\n" (Filename.remove_extension ml)

let pp_dep dir fmt oo =
  let open Coqdep in
  match oo with
  | VO vo -> pp_vo_dep dir fmt vo
  | MLG f -> pp_mlg_dep dir fmt f

let out_install fmt dir ff =
  let open Coqdep in
  let itarget = String.concat "/" dir in
  let ff = List.concat @@ pmap (function | VO vo -> Some (gen_coqc_targets vo) | _ -> None) ff in
  let pp_ispec fmt tg = fprintf fmt "(%s as coq/%s)" tg (bpath [itarget;tg]) in
  fprintf fmt "(install@\n @[(section lib_root)@\n(package coq)@\n(files @[%a@])@])@\n"
    (pp_list pp_ispec sep) ff

(* For each directory, we must record two things, the build rules and
   the install specification. *)
let record_dune d ff =
  let sd = bpath d in
  if Sys.file_exists sd && Sys.is_directory sd then
    let out = open_out (bpath [sd;"dune"]) in
    let fmt = formatter_of_out_channel out in
    if List.nth d 0 = "plugins" || List.nth d 0 = "user-contrib" then
      fprintf fmt "(include plugin_base.dune)@\n";
    out_install fmt d ff;
    List.iter (pp_dep d fmt) ff;
    fprintf fmt "%!";
    close_out out
  else
    eprintf "error in coq_dune, a directory disappeared: %s@\n%!" sd

(* File Scanning *)
let scan_mlg ~root m d =
  let open Coqdep in
  let dir = [root; d] in
  let m = DirMap.add dir [] m in
  let mlg = Sys.(List.filter (fun f -> Filename.(check_suffix f ".mlg"))
                   Array.(to_list @@ readdir (bpath dir))) in
  List.fold_left (fun m f -> add_map_list [root; d] (MLG f) m) m mlg

let scan_dir ~root m =
  let is_plugin_directory dir = Sys.(is_directory dir && file_exists (bpath [dir;"plugin_base.dune"])) in
  let dirs = Sys.(List.filter (fun f -> is_plugin_directory @@ bpath [root;f]) Array.(to_list @@ readdir root)) in
  List.fold_left (scan_mlg ~root) m dirs

let scan_plugins m = scan_dir ~root:"plugins" m
let scan_usercontrib m = scan_dir ~root:"user-contrib" m

let rec read_vfiles ic map =
  match
    try Some (Coqdep.parse_coqdep_line (input_line ic))
    with End_of_file -> None
  with
  | None -> map
  | Some rule ->
    (* Add vo_entry to its corresponding map entry *)
    let map = option_cata map (fun (dir, vo) -> add_map_list dir vo map) rule in
    read_vfiles ic map

let out_map map =
  DirMap.iter record_dune map

let exec_ifile f =
  match Array.length Sys.argv with
  | 1 -> f stdin
  | 2 ->
    let in_file = Sys.argv.(1) in
    begin try
      let ic = open_in in_file in
      (try f ic
       with _ -> eprintf "Error: exec_ifile@\n%!"; close_in ic)
      with _ -> eprintf "Error: cannot open input file %s@\n%!" in_file
    end
  | _ -> eprintf "Error: wrong number of arguments@\n%!"; exit 1

(*
let _ =
  exec_ifile (fun ic ->
      let map = scan_plugins DirMap.empty in
      let map = scan_usercontrib map in
      let map = read_vfiles ic map in
      out_map map)
*)
let _ =
  let out = open_out "test_suite_rules.sexp" in
  close_out out
