/- GID: D5/S0/Carrier/NormPowers
   generality: I
   mirror-B: D5/B/S0/Carrier/NormPowers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden norm preserves natural powers through its monoid homomorphism. -/

import D5.S0.Carrier.Norm

namespace D5.S0.Carrier

/-- The golden norm preserves natural powers. -/
theorem norm_pow (x : GoldenInt) (n : ℕ) : norm (x ^ n) = norm x ^ n := by
  exact normMonoidHom.map_pow x n

example (n : ℕ) : norm (phi ^ n) = (-1 : ℤ) ^ n := by
  simpa using norm_pow phi n

example (x : GoldenInt) : norm (x ^ 2) = norm x ^ 2 := by
  simpa using norm_pow x 2

end D5.S0.Carrier
