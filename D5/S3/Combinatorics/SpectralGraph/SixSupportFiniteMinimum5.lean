/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum5
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum5
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum5.actual_application; instance=D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum5.result
   digest: Complete 3486-pair minimum-5 endpoint certificate and actual ideal-graph application. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteEndpointBase

/-! Complete original integer domain, not a sampled or bounded substitute for
an infinite classification. The uniform cutoff handles the remaining tail. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteMinimum5

open SixSupportFiniteEndpointBase SixSupportIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Both possible integer low-root endpoints are nonzero at every original pair. -/
theorem result : base 5 = true := by decide +kernel

/-- The full source domain has exactly 3486 distinct parameter positions. -/
theorem domain_card : (domain 5).length = 3486 := by decide +kernel

/-- Actual finite ideal graphs consume every pair of the complete certificate. -/
theorem actual_application (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 5 < b) (hbc : b < c)
    (hc : c < cutoff 5) :
    ¬ActualLaplacianIntegral (modulus p (exponents 5 b c)) :=
  actual_nonintegral p hp hinj 5 b c (by decide) hb hbc hc result

#print axioms result
#print axioms domain_card
#print axioms actual_application

end D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteMinimum5
