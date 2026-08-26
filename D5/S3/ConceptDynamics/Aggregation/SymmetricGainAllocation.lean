/- GID: D5/S3/ConceptDynamics/Aggregation/SymmetricGainAllocation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/SymmetricGainAllocation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal gains above a feasible disagreement point uniquely split the residual resource. -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Library-search audit trail (2026-08-27):
   * Repository searches for bargaining, disagreement points, symmetric gains,
     surplus splits, and the atom's coordinate formulas found no exact theorem.
   * The existing aggregation family contains collective-choice results, but no
     two-party resource allocation or disagreement-anchor primitive.
   * Pinned Mathlib has no exact theorem packaging this unique allocation. The
     proof uses its real linear arithmetic and ring normalization directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Aggregation.SymmetricGainAllocation

/-- For a feasible two-party disagreement point, there is a unique efficient
allocation with equal gains. Both coordinates and both anchor-relative gains
are exposed in the public predicate. -/
theorem symmetric_gain_allocation
    (d1 d2 : Real) (feasible : d1 + d2 <= 1) :
    ∃! allocation : Real × Real,
      allocation.1 + allocation.2 = 1 ∧
        allocation.1 - d1 = allocation.2 - d2 ∧
        allocation.1 = d1 + (1 - d1 - d2) / 2 ∧
        allocation.2 = d2 + (1 - d1 - d2) / 2 ∧
        allocation.1 - d1 = (1 - d1 - d2) / 2 ∧
        allocation.2 - d2 = (1 - d1 - d2) / 2 ∧
        0 <= (1 - d1 - d2) / 2 := by
  refine ⟨(d1 + (1 - d1 - d2) / 2, d2 + (1 - d1 - d2) / 2), ?_, ?_⟩
  · refine ⟨by ring, by ring, rfl, rfl, by ring, by ring, ?_⟩
    linarith
  · intro allocation properties
    rcases properties with ⟨_, _, firstCoordinate, secondCoordinate, _, _, _⟩
    apply Prod.ext
    · simpa only using firstCoordinate
    · simpa only using secondCoordinate

#print axioms symmetric_gain_allocation

end D5.S3.ConceptDynamics.Aggregation.SymmetricGainAllocation
