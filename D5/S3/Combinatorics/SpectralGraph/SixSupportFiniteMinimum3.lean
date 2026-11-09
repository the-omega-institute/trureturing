/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum3
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum3.actual_application; instance=D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteMinimum3.result
   digest: Complete 325-pair minimum-3 endpoint certificate and actual ideal-graph application. -/

import D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteEndpointBase

/-! Complete original integer domain, not a sampled or bounded substitute for
an infinite classification. The uniform cutoff handles the remaining tail. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteMinimum3

open SixSupportFiniteEndpointBase SixSupportIdealIntersectionLift
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Both possible integer low-root endpoints are nonzero at every original pair. -/
theorem result : base 3 = true := by decide +kernel

/-- The full source domain has exactly 325 distinct parameter positions. -/
theorem domain_card : (domain 3).length = 325 := by decide +kernel

/-- The full original minimum-three first-endpoint sign count. -/
theorem positive_count : (domain 3).countP (fun t => 0 < SixSupportClassificationAlgebra.value
    (3 : ℤ) (t.1 : ℤ) (t.2 : ℤ) 1) = 257 := by decide +kernel

/-- Every remaining original minimum-three first endpoint is negative. -/
theorem negative_count : (domain 3).countP (fun t => SixSupportClassificationAlgebra.value
    (3 : ℤ) (t.1 : ℤ) (t.2 : ℤ) 1 < 0) = 68 := by decide +kernel

/-- Actual finite ideal graphs consume every pair of the complete certificate. -/
theorem actual_application (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (b c : ℕ) (hb : 3 < b) (hbc : b < c)
    (hc : c < cutoff 3) :
    ¬ActualLaplacianIntegral (modulus p (exponents 3 b c)) :=
  actual_nonintegral p hp hinj 3 b c (by decide) hb hbc hc result

#print axioms result
#print axioms domain_card
#print axioms actual_application

end D5.S3.Combinatorics.SpectralGraph.SixSupportFiniteMinimum3
