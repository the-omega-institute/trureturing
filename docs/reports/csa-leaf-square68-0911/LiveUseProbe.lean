import D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout
import Lean.Meta

/- Evidence for the preregistered consumer only. Reduction does not unfold named
   theorem constants and is not an automated semantic admission judgment. -/
open Lean Meta in
run_meta do
  let env := (← getEnv).setExporting false
  let name := `D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout.leaf_square_readout
  let some info := env.find? name | throwError "consumer missing"
  let some value := info.value? (allowOpaque := true) | throwError "proof missing"
  let reduced ← zetaReduce value
  let reduced ← Core.betaReduce reduced
  let reduced ← transform reduced (post := fun e => do
    let e' ← whnfCore e
    return if e' == e then .done e else .visit e')
  let used := reduced.getUsedConstants
  let required := #[
    `D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout.source_charge_apply,
    `D5.S3.ConceptDynamics.Spacetime.LeafSquareReadout.leaf_product_fiber_readout,
    `Finset.sum_mul_sum]
  for dependency in required do
    unless used.contains dependency do throwError "reduced proof lost {dependency}"
  IO.FS.writeFile "docs/reports/csa-leaf-square68-0911/reduced-use.json"
    ((Json.mkObj [
      ("consumer", toJson name.toString),
      ("reduction", toJson "Lean zetaReduce, Core.betaReduce, recursive whnfCore; no constant delta unfolding"),
      ("raw_value_constants", toJson (value.getUsedConstants.map Name.toString)),
      ("reduced_value_constants", toJson (used.map Name.toString)),
      ("required_constants_retained", toJson (required.map Name.toString)),
      ("limit", toJson "Constant retention corroborates the authored live derivation; it alone is not semantic liveness or an escape-witness certificate.")]).pretty ++ "\n")
