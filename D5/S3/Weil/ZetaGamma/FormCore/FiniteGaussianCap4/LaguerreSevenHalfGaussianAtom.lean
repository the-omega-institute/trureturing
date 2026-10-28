/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfGaussianAtom
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Gaussian generating-function helper for the original finite-source comparison. -/

/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED independent source proposal, 2026-10-26.
No compiler, kernel, or official acceptance is asserted.

Specialization to the actual Gaussian atom, not an abstract basis expansion.
Finite-source parity, mass, L2/graph limits, and cap4 assembly are not claimed.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfCauchy

set_option autoImplicit false

noncomputable section

namespace FiniteGaussianCap4.LaguerreSevenHalf

def gaussianSiteQ (a : ℝ) : ℝ :=
  (Real.exp (2 * a) - 1) / (Real.exp (2 * a) + 1)

def gaussianSiteAmplitude (a : ℝ) : ℝ :=
  Real.exp (9 * a / 2) * (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ)

theorem gaussianSiteQ_abs_lt_one (a : ℝ) : |gaussianSiteQ a| < 1 := by
  have ht : 0 < Real.exp (2 * a) := Real.exp_pos _
  have hd : 0 < Real.exp (2 * a) + 1 := by linarith
  change |(Real.exp (2 * a) - 1) / (Real.exp (2 * a) + 1)| < 1
  apply abs_lt.mpr
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem gaussianSiteQ_one_sub_pos (a : ℝ) : 0 < 1 - gaussianSiteQ a := by
  have hq := (abs_lt.mp (gaussianSiteQ_abs_lt_one a)).2
  linarith

theorem gaussianSiteQ_mobius (a : ℝ) :
    (1 + gaussianSiteQ a) / (1 - gaussianSiteQ a) = Real.exp (2 * a) := by
  have hd : Real.exp (2 * a) + 1 ≠ 0 := by positivity
  have hq : 1 - gaussianSiteQ a ≠ 0 := (gaussianSiteQ_one_sub_pos a).ne'
  apply (div_eq_iff hq).2
  dsimp [gaussianSiteQ]
  field_simp [hd]
  <;> ring

/-- No restriction on the real site: a radius with |q|<r<1 always exists. -/
theorem gaussianSiteQ_exists_radius (a : ℝ) :
    ∃ r : ℝ, 0 < r ∧ |gaussianSiteQ a| < r ∧ r < 1 := by
  refine ⟨(|gaussianSiteQ a| + 1) / 2, ?_, ?_, ?_⟩
  all_goals
    have hq := gaussianSiteQ_abs_lt_one a
    have hq0 := abs_nonneg (gaussianSiteQ a)
    linarith

/-- The concrete finite-source atom exp(9a/2-exp(2a)x), expanded pointwise.
No completeness theorem or expansion hypothesis occurs in this statement. -/
theorem gaussian_atom_hasSum (a x : ℝ) :
    HasSum (fun n : ℕ =>
      (gaussianSiteAmplitude a * phi x n) * gaussianSiteQ a ^ n)
      (Real.exp (9 * a / 2 - Real.exp (2 * a) * x)) := by
  have hq := gaussianSiteQ_abs_lt_one a
  have hs := (phi_hasSum_real x (gaussianSiteQ a) hq).mul_left
    (gaussianSiteAmplitude a)
  have hp : (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (gaussianSiteQ_one_sub_pos a) _).ne'
  have hv : gaussianSiteAmplitude a *
      ((1 - gaussianSiteQ a) ^ (-9 / 2 : ℝ) *
        Real.exp (-x * (1 + gaussianSiteQ a) / (1 - gaussianSiteQ a))) =
      Real.exp (9 * a / 2 - Real.exp (2 * a) * x) := by
    rw [mul_div_assoc, gaussianSiteQ_mobius, gaussianSiteAmplitude,
      show (-9 / 2 : ℝ) = -(9 / 2 : ℝ) by ring,
      Real.rpow_neg (gaussianSiteQ_one_sub_pos a).le]
    calc
      Real.exp (9 * a / 2) * (1 - gaussianSiteQ a) ^ (9 / 2 : ℝ) *
          (((1 - gaussianSiteQ a) ^ (9 / 2 : ℝ))⁻¹ *
            Real.exp (-x * Real.exp (2 * a))) =
          Real.exp (9 * a / 2) * Real.exp (-x * Real.exp (2 * a)) := by
            field_simp [hp]
            <;> ring
      _ = Real.exp (9 * a / 2 - Real.exp (2 * a) * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [hv] at hs
  simpa only [mul_assoc] using hs

end FiniteGaussianCap4.LaguerreSevenHalf
