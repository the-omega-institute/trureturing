/- GID: D5/S3/HomologicalAlgebra/Solid/IntegerRounding
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/IntegerRounding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
Concrete integer rounding for a possible direct cancellation of M_Z/B_Z.
Truncated division has uniformly bounded additivity and binary-subdivision
defects, independent of the integer and the denominator. These defects can
therefore be absorbed in B_Z. This file does not yet construct the condensed
null-sequence action or assert quotient vanishing.
New proofs, Apache-2.0.
-/

namespace LightCondensed.Solid

theorem integerRounding_remainder_bound (x d : ℤ) (hd : 0 < d) :
    |x - d * x.tdiv d| < d := by
  rw [← Int.tmod_def, ← Int.natCast_natAbs, Int.natAbs_tmod]
  calc
    ((x.natAbs % d.natAbs : ℕ) : ℤ) < (d.natAbs : ℤ) := by
      exact_mod_cast Nat.mod_lt x.natAbs (Int.natAbs_pos.mpr (by omega))
    _ = d := by simp [abs_of_pos hd]

/-- The defect is bounded uniformly even for negative and unbounded integers. -/
theorem integerRounding_add_defect (x y d : ℤ) (hd : 0 < d) :
    |(x + y).tdiv d - x.tdiv d - y.tdiv d| ≤ 2 := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.mp (integerRounding_remainder_bound x d hd)
  obtain ⟨hy₁, hy₂⟩ := abs_lt.mp (integerRounding_remainder_bound y d hd)
  obtain ⟨hs₁, hs₂⟩ := abs_lt.mp (integerRounding_remainder_bound (x + y) d hd)
  rw [abs_le]
  constructor
  · by_contra h
    have he : (x + y).tdiv d - x.tdiv d - y.tdiv d ≤ -3 := by omega
    have hm := mul_le_mul_of_nonneg_left he (le_of_lt hd)
    nlinarith
  · by_contra h
    have he : 3 ≤ (x + y).tdiv d - x.tdiv d - y.tdiv d := by omega
    have hm := mul_le_mul_of_nonneg_left he (le_of_lt hd)
    nlinarith

/-- Uniform binary-child defect, used modulo bounded integer sequences. -/
theorem integerRounding_binary_defect (x d : ℤ) (hd : 0 < d) :
    |x.tdiv d - 2 * x.tdiv (2 * d)| ≤ 2 := by
  have h := integerRounding_add_defect x x (2 * d) (by omega)
  rw [← two_mul, Int.mul_tdiv_mul_of_pos _ _ (by norm_num : (0 : ℤ) < 2)] at h
  simpa only [two_mul, sub_sub] using h

theorem integerRounding_zero_of_abs_lt (x d : ℤ) (hd : 0 < d) (hx : |x| < d) :
    x.tdiv d = 0 := by
  apply Int.natAbs_eq_zero.mp
  rw [Int.natAbs_tdiv]
  apply Nat.div_eq_of_lt
  have h : (x.natAbs : ℤ) < (d.natAbs : ℤ) := by
    simpa [abs_of_pos hd] using hx
  exact_mod_cast h

theorem integerRounding_dyadic_eventually_zero (x : ℤ) (k : ℕ)
    (hk : x.natAbs ≤ k) : x.tdiv ((2 : ℤ) ^ k) = 0 := by
  apply integerRounding_zero_of_abs_lt _ _ (pow_pos (by norm_num) _)
  rw [← Int.natCast_natAbs]
  have h : x.natAbs < 2 ^ k := hk.trans_lt (Nat.lt_two_pow_self (n := k))
  exact_mod_cast h

theorem integerRounding_preserves_bound (x d N : ℤ) (hx : |x| ≤ N) :
    |x.tdiv d| ≤ N := by
  calc
    |x.tdiv d| ≤ |x| := by
      simpa only [← Int.natCast_natAbs] using
        (Int.ofNat_le.mpr (Int.natAbs_tdiv_le_natAbs x d))
    _ ≤ N := hx

end LightCondensed.Solid
