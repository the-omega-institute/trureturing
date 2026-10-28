import D5.S3.Observer.CubicGain.PrimitivePrefix
import Lean.Meta.Reduce
import Lean.Elab.Command

/-! Transient inspection of normalized compiled proof dependencies. -/

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  let selected := ["whole_word_primitive_representation", "primitive_generator",
    "integer_oriented_kernel", "signs_trace", "polar_signs", "affine_nonneg",
    "slope_nonneg", "primitive_levels", "levels_converse", "kernel_rank",
    "traceAugment_det", "trace_cofactor", "pair_span", "pair_gcd",
    "nonnegative_rank_one_factor", "primitive_pair", "endpoint_arithmetic",
    "arithmetic_mul", "triangular_diagonal", "coefficients_value", "polar_expand"]
  let own := fun n : Name => n.toString.startsWith "D5.S3.Observer.CubicGain.PrimitivePrefix." ||
    n.toString.startsWith "_private.D5.S3.Observer.CubicGain.PrimitivePrefix."
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if own name && selected.any (fun s => name.toString.endsWith ("." ++ s)) then
      if let some value := info.value? (allowOpaque := true) then
        let reduced ← withTransparency .reducible <| reduce value false true false
        let deps := reduced.getUsedConstants.filter own
        rows := rows.push <| Json.mkObj [
          ("declaration", toJson name.toString),
          ("normalized_direct_new_dependencies", toJson (deps.map Name.toString))]
  let some output ← liftM <| IO.getEnv "PRIMITIVE_PREFIX_LIVE_OUTPUT"
    | throwError "PRIMITIVE_PREFIX_LIVE_OUTPUT is required"
  liftM <| IO.FS.writeFile output (Json.pretty (Json.arr rows))
