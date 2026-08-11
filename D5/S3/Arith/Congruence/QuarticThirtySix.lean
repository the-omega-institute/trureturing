/- GID: D5/S3/Arith/Congruence/QuarticThirtySix
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/QuarticThirtySix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The quartic m(k) = 27k⁴+108k³+171k²+126k+36 is divisible by 36 for every integer k, a polynomial congruence identity proved by evaluating the residue over ZMod 36. -/

import Mathlib

namespace D5.S3.Arith.Congruence.QuarticThirtySix

/-- The E.29 quartic `m(k) = 27k⁴ + 108k³ + 171k² + 126k + 36`. -/
def m (k : ℤ) : ℤ := 27 * k ^ 4 + 108 * k ^ 3 + 171 * k ^ 2 + 126 * k + 36

/-- `36 ∣ m(k)` for every integer `k`: the quartic vanishes identically modulo 36. -/
theorem thirtySix_dvd_m (k : ℤ) : (36 : ℤ) ∣ m k := by
  have h : ∀ r : ZMod 36, 27 * r ^ 4 + 108 * r ^ 3 + 171 * r ^ 2 + 126 * r + 36 = 0 := by decide
  have hcast : ((m k : ℤ) : ZMod 36) = 0 := by
    unfold m; push_cast; ring_nf; ring_nf at h; exact h _
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast

end D5.S3.Arith.Congruence.QuarticThirtySix
