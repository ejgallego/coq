(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let separator_hack = ref true

let filename_concat dir name =
  if !separator_hack
  then System.(dir // name)
  else Filename.concat dir name

(* This is used to overcome makefile limitations w.r.t. filenames,
   (bar/../foo is not the same than ./foo for make) but it is a crude
   hack and we should remove it, and instead require users to follow
   the same naming convention *)
let canonize vAccu f =
  let f' = filename_concat (Loadpath.absolute_dir (Filename.dirname f)) (Filename.basename f) in
  match List.filter (fun (_,full) -> f' = full) vAccu with
    | (f,_) :: _ -> f
    | _ -> f

let file_name s = function
  | None     -> s
  | Some d   -> filename_concat d s

module State = struct
  type t = Loadpath.State.t
  let loadpath x = x
end

let compute_deps ~meta_files vAccu st =
  let mk_dep (name, _orig_path) =
    let canonize = canonize vAccu in
    let deps = File_analysis.find_dependencies ~canonize ~meta_files st name in
    Dep_info.make ~name ~deps in
  vAccu |> List.rev |> List.map mk_dep

(** Coq files specifies on the command line:
    - [vAccu : (string * string) list]
    - first string is the full filename, with only its extension removed
    - second string is the absolute version of the previous (via getcwd)
*)
type vAccu = (string * string) list

let rec treat_file vAccu old_dirname old_name =
  let name = Filename.basename old_name
  and new_dirname = Filename.dirname old_name in
  let dirname =
    match (old_dirname,new_dirname) with
      | (d, ".") -> d
      (* EGJA: We should disable this buggy normalization stuff for
         "./foo -> foo" but it breaks dune coq.theory! *)
      | (None,d) -> Some d
      | (Some d1,d2) -> Some (filename_concat d1 d2)
  in
  let complete_name = file_name name dirname in
  let stat_res =
    try Unix.stat complete_name
    with Unix.Unix_error(error, _, _) ->
      Error.cannot_open complete_name (Unix.error_message error)
  in
  match stat_res.Unix.st_kind with
  | Unix.S_DIR ->
    (if name.[0] <> '.' then
       let newdirname =
         match dirname with
         | None -> name
         | Some d -> filename_concat d name
       in
       Array.fold_left (fun vAccu file ->
           treat_file vAccu (Some newdirname) file) vAccu
         (Sys.readdir complete_name)
    else vAccu)
  | Unix.S_REG ->
    (match Loadpath.get_extension name [".v"] with
     | base,".v" ->
       let name = file_name base dirname in
       let absname = Loadpath.absolute_file_name ~filename_concat base dirname in
       (name, absname) :: vAccu
     | _ -> vAccu)
  | _ -> vAccu

let treat_file_command_line vAccu old_name =
  treat_file vAccu None old_name

let treat_file_coq_project vAccu where old_name =
  treat_file vAccu None old_name

let warn_project_file =
  let category = CWarnings.CoreCategories.filesystem in
  CWarnings.create ~name:"project-file" ~category Pp.str

let treat_coqproject st f =
  let open CoqProject_file in
  let iter_sourced f = List.iter (fun {thing} -> f thing) in
  let fold_sourced f = List.fold_left (fun acc {thing} -> f acc thing) in
  let project =
    try read_project_file ~warning_fn:warn_project_file f
    with
    | Parsing_error msg -> Error.cannot_parse_project_file f msg
    | UnableToOpenProjectFile msg -> Error.cannot_open_project_file msg
  in
  (* EJGA: This should add to findlib search path *)
  (* iter_sourced (fun { path } -> Loadpath.add_caml_dir st path) project.ml_includes; *)
  iter_sourced (fun ({ path }, l) -> Loadpath.add_q_include st path l) project.q_includes;
  iter_sourced (fun ({ path }, l) -> Loadpath.add_r_include st path l) project.r_includes;
  fold_sourced (fun acc f' -> treat_file_coq_project acc f f')
    [] (all_files project)

let add_include st (rc, r, ln) =
  if rc then
    Loadpath.add_r_include st r ln
  else
    Loadpath.add_q_include st r ln

let init ~make_separator_hack args =
  separator_hack := make_separator_hack;
  if not Coq_config.has_natdynlink then Makefile.set_dyndep "no";
  let st = Loadpath.State.make () in
  Makefile.set_write_vos args.Args.vos;
  Makefile.set_noglob args.Args.noglob;
  let vAccu = Option.cata (treat_coqproject st) [] args.Args.coqproject in
  (* EJGA: This should add to findlib search path *)
  (* List.iter (Loadpath.add_caml_dir st) args.Args.ml_path; *)
  List.iter (add_include st) args.Args.vo_path;
  Makefile.set_dyndep args.Args.dyndep;
  st, vAccu, args.Args.meta_files
