import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema
import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve
import Lean.Util.FoldConsts

/- Transient exact statement/dependency evidence; no delivered declaration. -/
set_option pp.universes true
set_option pp.proofs false
set_option maxRecDepth 10000

open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let targets : Array Name := #[
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.GM3_three_closed,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree.GM3_three_behavior,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeBalancing.pair_mixing,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.curve_minimum,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.curve_boundaries,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.curve_derivative,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve.physical_curve_minimum,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.integer_extrema,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.GM3_three_extrema,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema.extremal_degeneracy,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeMajorization.schur_comparison,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.value_swap,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.value_cycle,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.parameter_behavior,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.value_eq_log_ratio,
    `D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeScalar.value_neg]
  let env ← getEnv
  for target in targets do
    let ci ← getConstInfo target
    logInfo m!"NI_EXACT_STATEMENT {target} : {ci.type}"
    let direct := ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
    logInfo m!"NI_DIRECT_CONSTANTS {target} {direct}"
    let mut seen : NameSet := {}
    let mut todo := direct.toList
    let mut project : Array Name := #[]
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let text := n.toString
      if text.startsWith "D5." || text.startsWith "_private.D5." then
        project := project.push n
        if let some info := env.find? n then
          if let some body := info.value? (allowOpaque := true) then
            todo := body.getUsedConstants.toList ++ todo
    logInfo m!"NI_TRANSITIVE_PROJECT_CONSTANTS {target} {project}"
    logInfo m!"NI_TRANSITIVE_PROJECT_CONSTANT_COUNT {target} {project.size}"

open D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThree in
example := GM3_three_behavior 1 1 1 (by norm_num) (by norm_num) (by norm_num)

open D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeExtrema in
example := GM3_three_extrema 3 (by norm_num) 2 (by norm_num)
  (fun _ => 1) (by intro i; norm_num) (by norm_num [Fin.sum_univ_three])

open D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaThreeCurve in
example := physical_curve_minimum 3 (by norm_num) (by norm_num) 2 (by norm_num)
  1 (by norm_num) (by norm_num)
