/- GID: D5/S3/Arith/Congruence/SineCharacterPeriodicity
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/SineCharacterPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sine at integer half-turns equals the quadratic character modulo four. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Tactic

namespace D5.S3.Arith.Congruence.SineCharacterPeriodicity

/-- At integer half-turns, sine is the quadratic character modulo four: its values on residues
`0, 1, 2, 3` are respectively `0, 1, 0, -1`. This is the explicit character bridge in residual
remark 27.9; the two-squares representation formula and its Dirichlet-series corollaries are not
claimed here. -/
theorem sin_pi_mul_nat_div_two_eq_chi_four (n : ℕ) :
    Real.sin (Real.pi * (n : ℝ) / 2) = ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) := by
  have hn : (n : ℝ) = ((n % 4 : ℕ) : ℝ) + 4 * ((n / 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n 4).symm
  calc
    Real.sin (Real.pi * (n : ℝ) / 2) =
        Real.sin
          (Real.pi * ((n % 4 : ℕ) : ℝ) / 2 + (n / 4 : ℕ) * (2 * Real.pi)) := by
      congr 1
      rw [hn]
      ring
    _ = Real.sin (Real.pi * ((n % 4 : ℕ) : ℝ) / 2) :=
      Real.sin_add_nat_mul_two_pi _ _
    _ = ((ZMod.χ₄ ((n % 4 : ℕ) : ZMod 4) : ℤ) : ℝ) := by
      have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
      have hcases : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
      rcases hcases with h | h | h | h
      · rw [h]
        norm_num [ZMod.χ₄]
      · rw [h]
        norm_num [ZMod.χ₄]
      · rw [h]
        norm_num [ZMod.χ₄]
      · rw [h]
        norm_num [ZMod.χ₄]
        rw [show Real.pi * 3 / 2 = Real.pi / 2 + Real.pi by ring,
          Real.sin_add_pi, Real.sin_pi_div_two]
    _ = ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) := by
      norm_cast
      exact (ZMod.χ₄_nat_mod_four n).symm

end D5.S3.Arith.Congruence.SineCharacterPeriodicity
