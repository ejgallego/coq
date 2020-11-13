(* LICENSE NOTE: This file is dually MIT/LGPL 2.1+ licensed. MIT license:
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *)

open Format

(* Keeping this file self-contained as it is a "bootstrap" utility *)
(* Is OCaml missing these basic functions in the stdlib?           *)
let option_iter f o = match o with
  | Some x -> f x
  | None -> ()

let option_cata d f o = match o with
  | Some x -> f x
  | None -> d

let list_compare f = let rec lc x y = match x, y with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | x::xs, y::ys -> let r = f x y in if r = 0 then lc xs ys else r
  in lc

let rec pp_list pp sep fmt l = match l with
  | []  -> ()
  | [l] -> fprintf fmt "%a" pp l
  | x::xs -> fprintf fmt "%a%a%a" pp x sep () (pp_list pp sep) xs

let rec pmap f l = match l with
  | []  -> []
  | x :: xs ->
    begin match f x with
      | None -> pmap f xs
      | Some r -> r :: pmap f xs
    end

let sep fmt () = fprintf fmt "@;"

(* Creation of paths, aware of the platform separator. *)
let bpath l = String.concat Filename.dir_sep l

module DirOrd = struct
  type t = string list
  let compare = list_compare String.compare
end

module DirMap = Map.Make(DirOrd)

(* Functions available in newer OCaml versions *)
(* Taken from the OCaml std library (c) INRIA / LGPL-2.1 *)
module Legacy = struct


  (* Fix once we move to OCaml >= 4.06.0 *)
  let list_init len f =
    let rec init_aux i n f =
      if i >= n then []
      else let r = f i in r :: init_aux (i+1) n f
    in init_aux 0 len f

  (* Slower version of DirMap.update, waiting for OCaml 4.06.0 *)
  let dirmap_update key f map =
    match begin
      try f (Some (DirMap.find key map))
      with Not_found -> f None
    end with
    | None   -> DirMap.remove key map
    | Some x -> DirMap.add key x map

end

let add_map_list key elem map =
  (* Move to Dirmap.update once we require OCaml >= 4.06.0 *)
  Legacy.dirmap_update key (fun l -> Some (option_cata [elem] (fun ll -> elem :: ll) l)) map

let replace_ext ~file ~newext =
  Filename.(remove_extension file) ^ newext
