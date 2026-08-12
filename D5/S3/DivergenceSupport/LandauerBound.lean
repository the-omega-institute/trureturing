/- GID: D5/S3/DivergenceSupport/LandauerBound
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/LandauerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An exact heat-entropy balance with nonnegative information and divergence remainders implies the thermodynamic lower bound by discarding those remainders. -/

import Mathlib

namespace D5.S3.DivergenceSupport.LandauerBound

/-- An exact heat-entropy balance implies the thermodynamic lower bound after its nonnegative
mutual-information and divergence remainders are discarded. -/
theorem landauer_bound_of_balance
    (beta heat entropyChange mutualInfo divergence : ℝ)
    (hbalance : beta * heat = -entropyChange + mutualInfo + divergence)
    (hmutualInfo : 0 ≤ mutualInfo) (hdivergence : 0 ≤ divergence) :
    -entropyChange ≤ beta * heat := by
  rw [hbalance]
  simpa [add_assoc] using
    (le_add_of_nonneg_right (add_nonneg hmutualInfo hdivergence) :
      -entropyChange ≤ -entropyChange + (mutualInfo + divergence))

end D5.S3.DivergenceSupport.LandauerBound
