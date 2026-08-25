/- GID: D5/S3/ConceptDynamics/Causal/BenefitProbabilityBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/BenefitProbabilityBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean potential-outcome marginals bound the benefit mass from both sides. -/

import D5.S3.ConceptDynamics.Causal.PrincipalStrata

/- Library-search audit trail (2026-08-26):
   * `PrincipalStrata` is the frozen predecessor using the canonical joint-mass
     carrier on Boolean potential-outcome pairs and is imported directly.
   * Repository searches for the benefit mass together with the displayed
     maximum and minimum bounds found no existing declaration.
   * Pinned Mathlib searches found general linear-order minimum and maximum
     lemmas but no potential-outcome or benefit-probability theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.BenefitProbabilityBounds

/-- For any normalized nonnegative joint mass on Boolean potential outcomes,
the benefit mass is bounded below by the positive part of the marginal
difference and above by both available marginal masses. -/
theorem benefit_probability_bounds
    (mass : Bool × Bool -> Real)
    (mass_nonnegative : forall pair, 0 <= mass pair)
    (mass_total :
      mass (false, false) + mass (false, true) +
          mass (true, false) + mass (true, true) = 1) :
    max 0
        ((mass (false, true) + mass (true, true)) -
          (mass (true, false) + mass (true, true))) <=
      mass (false, true) /\
      mass (false, true) <=
        min (mass (false, true) + mass (true, true))
          (1 - (mass (true, false) + mass (true, true))) := by
  constructor
  · rw [max_le_iff]
    constructor
    · exact mass_nonnegative _
    · linarith [mass_nonnegative (true, false)]
  · rw [le_min_iff]
    constructor
    · linarith [mass_nonnegative (true, true)]
    · linarith [mass_nonnegative (false, false), mass_total]

#print axioms benefit_probability_bounds

end D5.S3.ConceptDynamics.Causal.BenefitProbabilityBounds
