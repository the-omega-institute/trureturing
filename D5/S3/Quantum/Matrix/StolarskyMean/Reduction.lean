/- GID: D5/S3/Quantum/Matrix/StolarskyMean/Reduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/StolarskyMean/Reduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Analytic.IsolatedZeros, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp]
   utility: none
   digest: Stolarsky profiles and logarithmic positive kernel pullbacks. -/

import D5.S3.Quantum.Matrix.StolarskyMean.Spectral
import D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Homogeneous logarithmic profiles and their mixed derivatives. -/

noncomputable section
open Finset Matrix
open scoped BigOperators Topology

namespace D5.S3.Quantum.Matrix.StolarskyMean.Reduction

open Defs

/-- The Stolarsky mean on a symmetric exponential pair. -/
def psi (γ t : ℝ) : ℝ := stolarsky γ (Real.exp (-t)) (Real.exp t)

/-- The second derivative defect of the exponential Stolarsky profile. -/
def f (γ t : ℝ) : ℝ := deriv (deriv (psi γ)) t - psi γ t

theorem stolarsky_symm (γ a b : ℝ) : stolarsky γ a b = stolarsky γ b a := by
  by_cases hab : a = b
  · subst b; rfl
  have hba : b ≠ a := Ne.symm hab
  simp only [stolarsky, if_neg hab, if_neg hba]
  split_ifs with hγ0 hγ1
  · rw [show b - a = -(a - b) by ring,
      show Real.log b - Real.log a = -(Real.log a - Real.log b) by ring,
      neg_div_neg_eq]
  · congr 1
    rw [show b - a = -(a - b) by ring,
      show b * Real.log b - a * Real.log a = -(a * Real.log a - b * Real.log b) by ring,
      neg_div_neg_eq]
  · congr 1
    rw [show b ^ γ - a ^ γ = -(a ^ γ - b ^ γ) by ring,
      show γ * (b - a) = -(γ * (a - b)) by ring, neg_div_neg_eq]

private theorem powerDividedDifference_pos {γ a b : ℝ}
    (hγ : γ ≠ 0) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < (a ^ γ - b ^ γ) / (γ * (a - b)) := by
  rcases lt_or_gt_of_ne hγ with hγ | hγ
  · rcases lt_or_gt_of_ne hab with hab | hba
    · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow_of_neg ha hab hγ))
        (mul_pos_of_neg_of_neg hγ (sub_neg.mpr hab))
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.rpow_lt_rpow_of_neg hb hba hγ))
        (mul_neg_of_neg_of_pos hγ (sub_pos.mpr hba))
  · rcases lt_or_gt_of_ne hab with hab | hba
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.rpow_lt_rpow ha.le hab hγ))
        (mul_neg_of_pos_of_neg hγ (sub_neg.mpr hab))
    · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow hb.le hba hγ))
        (mul_pos hγ (sub_pos.mpr hba))

theorem stolarsky_homogeneous (γ : ℝ) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    stolarsky γ (c * a) (c * b) = c * stolarsky γ a b := by
  by_cases hab : a = b
  · subst b; simp [stolarsky]
  have hcab : c * a ≠ c * b := fun h => hab ((mul_left_cancel₀ hc.ne') h)
  simp only [stolarsky, if_neg hab, if_neg hcab]
  split_ifs with hγ0 hγ1
  · rw [Real.log_mul hc.ne' ha.ne', Real.log_mul hc.ne' hb.ne']
    have he : Real.log c + Real.log a - (Real.log c + Real.log b) =
        Real.log a - Real.log b := by ring
    rw [he]
    ring
  · rw [Real.log_mul hc.ne' ha.ne', Real.log_mul hc.ne' hb.ne']
    have he :
        (c * a * (Real.log c + Real.log a) - c * b * (Real.log c + Real.log b)) /
            (c * a - c * b) - 1 =
          Real.log c + ((a * Real.log a - b * Real.log b) / (a - b) - 1) := by
      field_simp [hc.ne', sub_ne_zero.mpr hab, sub_ne_zero.mpr hcab]
      ring
    rw [he, Real.exp_add, Real.exp_log hc]
  · rw [Real.mul_rpow hc.le ha.le, Real.mul_rpow hc.le hb.le]
    have he : (c ^ γ * a ^ γ - c ^ γ * b ^ γ) / (γ * (c * a - c * b)) =
        c ^ (γ - 1) * ((a ^ γ - b ^ γ) / (γ * (a - b))) := by
      rw [Real.rpow_sub hc, Real.rpow_one]
      field_simp [hc.ne', sub_ne_zero.mpr hab, hγ0, sub_ne_zero.mpr hcab]
    rw [he, Real.mul_rpow (Real.rpow_pos_of_pos hc _).le
      (powerDividedDifference_pos hγ0 ha hb hab).le,
      ← Real.rpow_mul hc.le]
    have hγ : γ - 1 ≠ 0 := sub_ne_zero.mpr hγ1
    rw [show (γ - 1) * (1 / (γ - 1)) = 1 by field_simp [hγ], Real.rpow_one]

theorem stolarsky_pos {γ a b : ℝ} (hγ : 2 ≤ γ) (ha : 0 < a) (hb : 0 < b) :
    0 < stolarsky γ a b := by
  by_cases hab : a = b
  · simpa [stolarsky, hab] using ha
  have hγ0 : γ ≠ 0 := by linarith
  have hγ1 : γ ≠ 1 := by linarith
  simp only [stolarsky, if_neg hab, if_neg hγ0, if_neg hγ1]
  apply Real.rpow_pos_of_pos
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.rpow_lt_rpow ha.le hab (by linarith)))
      (mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hab))
  · exact div_pos (sub_pos.mpr (Real.rpow_lt_rpow hb.le hba (by linarith)))
      (mul_pos (by linarith) (sub_pos.mpr hba))

theorem stolarsky_two (a b : ℝ) : stolarsky 2 a b = (a + b) / 2 := by
  by_cases hab : a = b
  · subst b; simp [stolarsky]
  simp only [stolarsky, if_neg hab]
  norm_num only [OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceIte, Real.rpow_two,
    sub_self, sub_zero, one_div_one, Real.rpow_one]
  field_simp [sub_ne_zero.mpr hab]
  ring

theorem conditionallyNegative_two {n : ℕ} (l : Fin n → ℝ) :
    Spectral.ConditionallyNegative (stolarskyMatrix 2 l) := by
  intro c hc
  change (∑ i, c i * ∑ j, stolarsky 2 (l i) (l j) * c j) ≤ 0
  have he (i j : Fin n) : c i * (((l i + l j) / 2) * c j) =
      (c i * l i / 2) * c j + c i * (c j * l j / 2) := by ring
  simp_rw [stolarsky_two, Finset.mul_sum, he, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hc, mul_zero, zero_mul, add_zero]
  exact le_rfl

theorem inClassA_two {n : ℕ} (l : Fin (n + 1) → ℝ) (hl : ∀ i, 0 < l i) :
    InClassA (stolarskyMatrix 2 l) := by
  apply Spectral.inClassA_of_conditionallyNegative
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial, stolarskyMatrix] using stolarsky_symm 2 (l j) (l i)
  · exact fun i j => stolarsky_pos (by norm_num) (hl i) (hl j)
  · exact conditionallyNegative_two l

def profileKernel (g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  Real.sqrt a * Real.sqrt b * g ((Real.log b - Real.log a) / 2)

theorem stolarsky_eq_profileKernel (γ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    stolarsky γ a b = profileKernel (psi γ) a b := by
  let m := (Real.log a + Real.log b) / 2
  let t := (Real.log b - Real.log a) / 2
  have hea : Real.exp m * Real.exp (-t) = a := by
    rw [← Real.exp_add, show m + -t = Real.log a by dsimp [m, t]; ring,
      Real.exp_log ha]
  have heb : Real.exp m * Real.exp t = b := by
    rw [← Real.exp_add, show m + t = Real.log b by dsimp [m, t]; ring,
      Real.exp_log hb]
  have hec : Real.exp m = Real.sqrt a * Real.sqrt b := by
    have hsq : Real.exp m ^ 2 = a * b := by
      rw [pow_two, ← Real.exp_add,
        show m + m = Real.log a + Real.log b by dsimp [m]; ring,
        Real.exp_add, Real.exp_log ha, Real.exp_log hb]
    have hsq' : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
      rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    nlinarith [Real.exp_pos m, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have h := stolarsky_homogeneous γ (Real.exp_pos (-t)) (Real.exp_pos t) (Real.exp_pos m)
  rw [hea, heb, hec] at h
  exact h

/-- Positive definiteness survives logarithmic coordinates and the diagonal
weight needed by the negative mixed derivative. -/
theorem logarithmic_pullback_nonneg {g : ℝ → ℝ}
    (hg : D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion.PositiveDefinite
      (fun t => (g t : ℂ))) {n : ℕ} (a c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      (g ((Real.log (a i) - Real.log (a j)) / 2) /
        (4 * Real.sqrt (a i) * Real.sqrt (a j))) := by
  have h := (hg n (fun i => -Real.log (a i) / 2)).re_dotProduct_nonneg
    (fun i => ((c i / (2 * Real.sqrt (a i)) : ℝ) : ℂ))
  change 0 ≤ Complex.re _ at h
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def,
    Complex.conj_ofReal, Finset.mul_sum, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -Real.log (a j) / 2 - -Real.log (a i) / 2 =
      (Real.log (a i) - Real.log (a j)) / 2 by ring]
  ring

end D5.S3.Quantum.Matrix.StolarskyMean.Reduction
