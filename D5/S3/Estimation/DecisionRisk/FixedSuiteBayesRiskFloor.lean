/- GID: D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-suite learners have average risk at least the suite's Bayes floor. -/

/- Library-search audit trail (2026-08-14):
   * Exact pinned-mathlib hit: `ProbabilityTheory.bayesRisk_le_avgRisk` states that
     Bayes risk is at most the average risk of every Markov estimator.
   * Searches for `bayesRisk`, `avgRisk`, the round-indexed form, and the finite-suite
     form found no theorem in `D5/` with the statement below.
   * A search of the other pinned Lean packages found no independent definition or theorem
     with this shape. The proof applies the mathlib result directly and does not reprove it.
-/

import Mathlib.Probability.Decision.Risk.Basic

namespace D5.S3.Estimation.DecisionRisk.FixedSuiteBayesRiskFloor

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- At every round, a learner whose only input is the same `m`-entry observation suite has
average deployment risk at least the Bayes risk available from that suite. -/
theorem fixed_suite_bayes_risk_floor
    {Theta X Y : Type*} [MeasurableSpace Theta] [MeasurableSpace X] [MeasurableSpace Y]
    (m : Nat) (loss : Theta -> Y -> ENNReal) (suite : Kernel Theta (Fin m -> X))
    (learner : Nat -> Kernel (Fin m -> X) Y) (pi : Measure Theta) (k : Nat)
    [IsMarkovKernel (learner k)] :
    bayesRisk loss suite pi <= avgRisk loss suite (learner k) pi :=
  bayesRisk_le_avgRisk loss suite (learner k) pi

/-- A valid randomized-decision hypothesis is inhabited by the identity kernel. -/
example {Z : Type*} [MeasurableSpace Z] :
    IsMarkovKernel (Kernel.id : Kernel Z Z) := inferInstance

/-- A one-entry suite observation domain is inhabited. -/
example : Nonempty (Fin 1 -> Unit) := ⟨fun _ => ()⟩

#print axioms fixed_suite_bayes_risk_floor

end D5.S3.Estimation.DecisionRisk.FixedSuiteBayesRiskFloor
