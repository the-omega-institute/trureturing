/- GID: D5/S3/Quantum/Measurement/Auric/CompleteRecordBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CompleteRecordBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Feasible laws and sharp attained coherent record information for three unequal coordinate capacities. -/

import D5.S3.Quantum.Measurement.Auric.CompleteRecordBudgetAssembly
import D5.S3.Quantum.Measurement.Auric.UnequalGeometry

/-! The sharp budget of the labeled three-effect coherent projective record. -/

namespace D5.S3.Quantum.Measurement.Auric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At every admissible rank, exactly the feasible labeled laws occur. Every valid
certificate gives the attained information maximum and conditional entropy minimum
for the actual system–record state. -/
theorem complete_record_budget (c : ι → Fin 3) (r : ℕ) (q : Fin 3 → ℝ) :
    CompleteBudgetStatement c r q :=
  complete_budget_of_geometry c r q (unequal_geometry_statement c r q)

end D5.S3.Quantum.Measurement.Auric
