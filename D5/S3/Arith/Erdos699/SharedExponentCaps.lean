/- GID: D5/S3/Arith/Erdos699/SharedExponentCaps
   generality: G
   mirror-B: D5/B/S3/Arith/Erdos699/SharedExponentCaps
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact 11-23 shared-exponent residues and their four impossible lift rows. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Erdos699.SharedExponentCaps

/-- The base-two residues and the first common prime-power returns. -/
theorem prime_and_lift_residues :
    (2 : ℕ) ^ 8 % 11 = 3 ∧
      (2 : ℕ) ^ 8 % 23 = 3 ∧
      (2 : ℕ) ^ 10 % 121 = (1 + 5 * 11) % 121 ∧
      (2 : ℕ) ^ 110 % 121 = 1 ∧
      (2 : ℕ) ^ 10 % 11 = 1 ∧
      (2 : ℕ) ^ 11 % 23 = 1 := by
  norm_num

/-- The return modulo 121 first occurs at the 110-step exponent. -/
theorem first_return_mod_121 :
    ∀ z : ℕ, 0 < z → z < 11 → (2 : ℕ) ^ (10 * z) % 121 ≠ 1 := by
  intro z hzlt hz
  interval_cases z <;> norm_num

/-- The four second-lift rows cannot share one exponent. -/
theorem shared_lift_caps (N : ℕ) :
    (N % 110 ≠ 0 ∨ N % 11 ≠ 1) ∧
      (N % 110 ≠ 22 ∨ N % 11 ≠ 4) ∧
      (N % 110 ≠ 1 ∨ N % 11 ≠ 0) ∧
      (N % 110 ≠ 23 ∨ N % 11 ≠ 3) := by
  omega

end D5.S3.Arith.Erdos699.SharedExponentCaps
