/- GID: D5/S3/ArithUnits/PrimeModUnit
   generality: G
   mirror-B: D5/B/S3/ArithUnits/PrimeModUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An element modulo a prime is a unit exactly when it is nonzero. -/

import Mathlib.Algebra.Field.ZMod

namespace D5.S3.ArithUnits.PrimeModUnit

/-- In the residue ring modulo a prime, the units are exactly the nonzero elements. -/
theorem prime_modulus_is_unit_iff_ne_zero (p : ℕ) (hp : Nat.Prime p) (a : ZMod p) :
    IsUnit a ↔ a ≠ 0 := by
  letI := Fact.mk hp
  exact _root_.isUnit_iff_ne_zero (G₀ := ZMod p)

end D5.S3.ArithUnits.PrimeModUnit
