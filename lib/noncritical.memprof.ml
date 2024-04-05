exception Anomaly of string option * Pp.t (* System errors *)

[@@@ocaml.warning "-52"]
let noncritical = function
  | Sys.Break | Out_of_memory | Stack_overflow
  | Assert_failure _ | Match_failure _ | Anomaly _
  | Control.Timeout -> false
  | Invalid_argument "equal: functional value" -> false
  | _ -> not (Memprof_limits.is_interrupted ())
[@@@ocaml.warning "+52"]
