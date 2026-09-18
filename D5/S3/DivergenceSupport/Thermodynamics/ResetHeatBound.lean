/- GID: D5/S3/DivergenceSupport/Thermodynamics/ResetHeatBound
   generality: G
   mirror-B: D5/B/S3/DivergenceSupport/Thermodynamics/ResetHeatBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reset entropy reduction is bounded by scaled heat under an explicit balance. -/

import D5.S3.DivergenceSupport.LandauerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.DivergenceSupport.Thermodynamics.ResetHeatBound

open D5.S3.DivergenceSupport.LandauerBound

/-- Substitute minus the removed entropy for the memory's entropy change in the
existing balance bound. Physical applicability of the balance is a separate premise. -/
theorem reset_heat_bound (beta heat erasedEntropy mutualInfo divergence : Real)
    (hbalance : beta * heat = erasedEntropy + mutualInfo + divergence)
    (hmutualInfo : 0 ≤ mutualInfo) (hdivergence : 0 ≤ divergence) :
    erasedEntropy ≤ beta * heat := by
  simpa only [neg_neg] using
    landauer_bound_of_balance beta heat (-erasedEntropy) mutualInfo divergence
      (by simpa only [neg_neg] using hbalance) hmutualInfo hdivergence

#print axioms reset_heat_bound

end D5.S3.DivergenceSupport.Thermodynamics.ResetHeatBound
