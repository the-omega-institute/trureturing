/- GID: D5/S3/Arith/PrimeSquarePerfectPowerRepresentation
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeSquarePerfectPowerRepresentation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Every prime plus some square is a perfect power of exponent at least two. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace D5.S3.Arith.PrimeSquarePerfectPowerRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every prime is the difference between a perfect power and a square. -/
theorem result : ∀ p : ℕ, Nat.Prime p → ∃ x y n : ℕ, 2 ≤ n ∧ x ^ 2 + p = y ^ n := by
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | ⟨t, rfl⟩
  · exact ⟨5, 3, 3, by decide, by decide⟩
  · exact ⟨t, t + 1, 2, le_rfl, by ring⟩

end D5.S3.Arith.PrimeSquarePerfectPowerRepresentation
