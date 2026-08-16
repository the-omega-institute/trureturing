/- GID: D5/S3/Constants/Transcription/ConjugatePolynomialCertificate
   generality: I
   mirror-B: D5/B/S3/Constants/Transcription/ConjugatePolynomialCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor the exact kernel polynomial into conjugate golden quadratics. -/

/- Library-search audit trail (2026-08-17):
   * Exact coefficient and conjugate-factor searches found no complete result in D5 or pinned
     Mathlib.
   * Pinned Mathlib supplies `Real.sq_sqrt`, reused for the radical identity `sqrt 5 ^ 2 = 5`.
-/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace D5.S3.Constants.Transcription.ConjugatePolynomialCertificate

/-- The two conjugate quadratic factors from the source multiply to its exact quartic
certificate. This asserts the factorization only, not minimality or irreducibility. -/
theorem conjugate_quadratic_product (x : ℝ) :
    (x ^ 2 + (-810051203588 + 362265911296 * Real.sqrt 5) * x +
          (55406466168660996 - 24778524949233664 * Real.sqrt 5)) *
        (x ^ 2 + (-810051203588 - 362265911296 * Real.sqrt 5) * x +
          (55406466168660996 + 24778524949233664 * Real.sqrt 5)) =
      x ^ 4 - 1620102407176 * x ^ 3 + 110811693059397656 * x ^ 2 +
        84768625708978144 * x - 246295300782612464 := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  rw [hsqrt_sq]
  ring

#print axioms conjugate_quadratic_product

end D5.S3.Constants.Transcription.ConjugatePolynomialCertificate
