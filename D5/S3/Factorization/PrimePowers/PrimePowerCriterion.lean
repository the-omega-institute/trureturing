/- GID: D5/S3/Factorization/PrimePowers/PrimePowerCriterion
   generality: G
   mirror-B: D5/B/S3/Factorization/PrimePowers/PrimePowerCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime powers are exactly the naturals with one prime divisor. -/

import Mathlib.Data.Nat.Factorization.PrimePow

namespace D5.S3.Factorization.PrimePowers.PrimePowerCriterion

/- Pinned mathlib supplies the exact characterization
   `isPrimePow_iff_unique_prime_dvd`; this theorem is its repository-addressed wrapper. -/

/-- A natural number is a prime power exactly when it has a unique prime divisor. -/
theorem prime_power_iff_unique_prime_divisor (n : ℕ) :
    IsPrimePow n ↔ ∃! p : ℕ, p.Prime ∧ p ∣ n :=
  isPrimePow_iff_unique_prime_dvd

#print axioms prime_power_iff_unique_prime_divisor

end D5.S3.Factorization.PrimePowers.PrimePowerCriterion
