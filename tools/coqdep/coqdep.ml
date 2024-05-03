(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The basic parts of coqdep are in [Common]. *)
open Coqdeplib

let warn_home_dir =
  let category = CWarnings.CoreCategories.filesystem in
  CWarnings.create ~name:"cannot-locate-home-dir" ~category Pp.str

let coqdep () =
  let open Common in

  ignore (Feedback.(add_feeder (console_feedback_listener Format.err_formatter)));

  (* Initialize coqdep, add files to dependency computation *)
  if Array.length Sys.argv < 2 then Args.usage ();
  let args =
    Sys.argv
    |> Array.to_list
    |> List.tl
    |> Args.parse (Args.make ())
  in
  let v_files = args.Args.files in
  (* We are in makefile hack mode *)
  let make_separator_hack = true in
  let st, vAccu, meta_files = init ~make_separator_hack args in
  let lst = Common.State.loadpath st in
  let vAccu = List.fold_left treat_file_command_line vAccu v_files in

  (* XXX: All the code below is just setting loadpaths, refactor to
     Common coq.boot library *)
  (* Add current dir with empty logical path if not set by options above. *)
  (try ignore (Loadpath.find_dir_logpath (Sys.getcwd()))
   with Not_found -> Loadpath.add_current_dir lst ".");
  (* We don't setup any loadpath if the -boot is passed *)
  if not args.Args.boot then begin
    let env = Boot.Env.init () in
    let stdlib = Boot.Env.(stdlib env |> Path.to_string) in
    let plugins = Boot.Env.(plugins env |> Path.to_string) in
    let user_contrib = Boot.Env.(user_contrib env |> Path.to_string) in
    Loadpath.add_dir_coqlib lst ~implicit:true stdlib ["Coq"];
    Loadpath.add_dir_coqlib lst ~implicit:true plugins ["Coq"];
    if Sys.file_exists user_contrib then
      Loadpath.add_dir_coqlib lst ~implicit:false user_contrib [];
    let add_dir s = Loadpath.add_dir_coqlib lst ~implicit:false s [] in
    List.iter add_dir (Envars.xdg_dirs ~warn:warn_home_dir);
    List.iter add_dir Envars.coqpath
  end;
  if args.Args.sort then
    let canonize = Common.canonize vAccu in
    File_analysis.sort ~canonize (Common.State.loadpath st) (List.map fst vAccu)
  else
    compute_deps ~meta_files vAccu st
    |> List.iter (Makefile.print_dep Format.std_formatter)

let () =
  try
    coqdep ()
  with exn ->
    Format.eprintf "*** Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    exit 1
