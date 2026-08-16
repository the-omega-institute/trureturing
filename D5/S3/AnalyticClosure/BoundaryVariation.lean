/- GID: D5/S3/AnalyticClosure/BoundaryVariation
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/BoundaryVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The rational variation law tends to one third at the integer boundary. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches found no equivalent boundary-limit declaration.
   * Pinned Mathlib provides the exact general mechanism in `ContinuousAt.div`,
     together with continuity of powers and subtraction.
   * Two `smart_search.sh` semantic queries returned no declaration-name hit;
     no specialized theorem for this rational function was found.
-/

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

namespace D5.S3.AnalyticClosure.BoundaryVariation

open Filter Topology

/-- The rational variation law extends continuously to the integer boundary,
where its limiting value is exactly one third. -/
theorem boundary_variation_tendsto_one_third :
    Tendsto (fun beta : Real => (beta ^ 2 - beta - 1) / (beta ^ 2 - 1))
      (nhds 2) (nhds (1 / 3)) := by
  have hcontinuous :
      ContinuousAt (fun beta : Real => (beta ^ 2 - beta - 1) / (beta ^ 2 - 1)) 2 :=
    (((continuousAt_id.pow 2).sub continuousAt_id).sub continuousAt_const).div
      ((continuousAt_id.pow 2).sub continuousAt_const)
      (by norm_num)
  simpa only [show ((2 : Real) ^ 2 - 2 - 1) / (2 ^ 2 - 1) = 1 / 3 by norm_num]
    using hcontinuous.tendsto

#print axioms boundary_variation_tendsto_one_third

end D5.S3.AnalyticClosure.BoundaryVariation
