/- GID: D5/S3/Factorization/LogarithmicLength
   generality: G
   mirror-B: D5/B/S3/Factorization/LogarithmicLength
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-factor logarithmic length equals the logarithm of the decoded natural number. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

/- Provenance: thin honest wrapper over pinned mathlib's prime-factorization
   logarithm identity (`Real.log_nat_eq_sum_factorization`). -/

namespace D5.S3.Factorization.LogarithmicLength

/-- The logarithmic length read from the finitely supported prime
factorization of a natural number. -/
noncomputable def factorizationLogLength (n : ℕ) : ℝ :=
  n.factorization.sum fun p exponent => exponent * Real.log p

/-- The exponent-weighted prime-factor length is exactly the natural
logarithm. This is a thin honest wrapper around mathlib's
`Real.log_nat_eq_sum_factorization`, with the equality reversed to expose the
length readout on the left. -/
theorem factorization_log_length_eq_log (n : ℕ) :
    factorizationLogLength n = Real.log n :=
  (Real.log_nat_eq_sum_factorization n).symm

end D5.S3.Factorization.LogarithmicLength
