/- GID: D5/S3/ConceptDynamics/InterventionsExchange/CanonicalHarmedProbabilityBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/CanonicalHarmedProbabilityBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical harmed event obeys the sharp bounds from its two marginals. -/

import D5.S3.ConceptDynamics.InterventionBounds.HarmedProbabilityBounds

/- Library-search audit trail (2026-08-26):
   * Exact frozen family hit `harmed_probability_frechet_bound` states the
     source theorem on the joint Boolean probability measure and is applied
     directly.
   * Body-shape searches for the two marginal events and harmed event hit only
     that frozen predecessor and its withdrawn placement redo; no event or
     probability primitive is redeclared here.
   * Pinned Mathlib search for harmed-probability and Frechet-bound declarations
     found no exact theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.CanonicalHarmedProbabilityBounds

open MeasureTheory
open D5.S3.ConceptDynamics.InterventionBounds.HarmedProbabilityBounds

/-- The harmed event constructed from a joint Boolean potential-outcome law
lies between the sharp lower and upper bounds determined by its marginals. -/
theorem canonical_harmed_probability_frechet_bound
    (μ : Measure (Bool × Bool)) [IsProbabilityMeasure μ] :
    let p₀ := μ.real {ω | ω.1 = true}
    let p₁ := μ.real {ω | ω.2 = true}
    let h := μ.real {ω | ω.1 = true ∧ ω.2 = false}
    max 0 (p₀ - p₁) ≤ h ∧ h ≤ min p₀ (1 - p₁) := by
  exact harmed_probability_frechet_bound μ

#print axioms canonical_harmed_probability_frechet_bound

end D5.S3.ConceptDynamics.InterventionsExchange.CanonicalHarmedProbabilityBounds
