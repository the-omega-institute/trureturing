/- GID: D5/S3/Quantum/PositiveResolvent/LogisticDensityBounds
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logistic density definitions and verified derivative identities for the positive-resolvent bounds. -/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped BigOperators Interval
open Set MeasureTheory intervalIntegral

namespace D5.S3.Quantum.PositiveResolvent

noncomputable def ell (r : ℝ) : ℝ := (r ^ 2 + Real.pi ^ 2) / (1 + Real.exp r)

noncomputable def jfun (r : ℝ) : ℝ := Real.exp (2 * r) * (r ^ 2 + Real.pi ^ 2) / (1 + Real.exp r) ^ 2

private lemma one_add_exp_ne_zero (r : ℝ) : 1 + Real.exp r ≠ 0 := by
  positivity

private lemma ell_hasDerivAt (r : ℝ) :
    HasDerivAt ell
      ((2 * r * (1 + Real.exp r) - (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
        (1 + Real.exp r) ^ 2) r := by
  unfold ell
  have hnum := (hasDerivAt_id r).pow 2 |>.add (hasDerivAt_const r (Real.pi ^ 2))
  have hden := (hasDerivAt_const r (1 : ℝ)).add (Real.hasDerivAt_exp r)
  have h := hnum.div hden (one_add_exp_ne_zero r)
  exact h.congr_deriv (by dsimp; field_simp; ring)

private lemma jfun_hasDerivAt (r : ℝ) :
    HasDerivAt jfun
      (Real.exp (2 * r) *
        ((2 * r + 2 * (r ^ 2 + Real.pi ^ 2)) * (1 + Real.exp r) -
          2 * (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
          (1 + Real.exp r) ^ 3) r := by
  unfold jfun
  have he := (Real.hasDerivAt_exp (2 * r)).comp r
      ((hasDerivAt_const r 2).mul (hasDerivAt_id r))
  have hp := (hasDerivAt_id r).pow 2 |>.add (hasDerivAt_const r (Real.pi ^ 2))
  have hd := ((hasDerivAt_const r (1 : ℝ)).add (Real.hasDerivAt_exp r)).pow 2
  have h := (he.mul hp).div hd (pow_ne_zero 2 (one_add_exp_ne_zero r))
  exact h.congr_deriv (by dsimp; field_simp; ring)

@[simp] theorem ell_deriv_formula (r : ℝ) :
    deriv ell r =
      (2 * r * (1 + Real.exp r) - (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
        (1 + Real.exp r) ^ 2 :=
  (ell_hasDerivAt r).deriv

@[simp] theorem jfun_deriv_formula (r : ℝ) :
    deriv jfun r =
      (Real.exp (2 * r) *
        ((2 * r + 2 * (r ^ 2 + Real.pi ^ 2)) * (1 + Real.exp r) -
          2 * (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
          (1 + Real.exp r) ^ 3) :=
  (jfun_hasDerivAt r).deriv

theorem ell_reflection (r : ℝ) : ell r + ell (-r) = r ^ 2 + Real.pi ^ 2 := by
  unfold ell
  have he : Real.exp r ≠ 0 := Real.exp_ne_zero r
  rw [Real.exp_neg]
  field_simp
  ring

theorem ell_deriv_neg (r : ℝ) : deriv ell r < 0 := by
  rw [ell_deriv_formula]
  have hden : 0 < (1 + Real.exp r) ^ 2 := by positivity
  rw [div_neg_iff]
  by_cases hr : r ≤ 0
  · right
    have he : 0 < Real.exp r := Real.exp_pos r
    have hp : 0 < r ^ 2 + Real.pi ^ 2 := by positivity
    have hleft : 2 * r * (1 + Real.exp r) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hr)
        (by positivity)
    have hright : 0 < (r ^ 2 + Real.pi ^ 2) * Real.exp r := mul_pos hp he
    exact ⟨by nlinarith, hden⟩
  · right
    have hr' : 0 < r := lt_of_not_ge hr
    have he : 0 < Real.exp r := Real.exp_pos r
    have hE : 1 ≤ Real.exp r := (Real.one_le_exp_iff.mpr hr'.le)
    have hinv : (Real.exp r)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (Real.exp_pos r)).2 hE
    have hquad : 4 * r < r ^ 2 + Real.pi ^ 2 := by
      nlinarith [sq_nonneg (r - 2), Real.pi_gt_three]
    have hinner : 2 * r * (1 + (Real.exp r)⁻¹) < r ^ 2 + Real.pi ^ 2 := by
      nlinarith [mul_nonneg (le_of_lt hr') (sub_nonneg.mpr hinv)]
    have hprod := mul_lt_mul_of_pos_right hinner he
    field_simp [ne_of_gt he] at hprod
    exact ⟨by
      calc
        2 * r * (1 + Real.exp r) - (r ^ 2 + Real.pi ^ 2) * Real.exp r
            = 2 * r * (Real.exp r + 1) - Real.exp r * (r ^ 2 + Real.pi ^ 2) := by ring
        _ < 0 := sub_neg.mpr hprod, hden⟩

private lemma jfun_gap_bracket_pos (r : ℝ) :
    0 < r ^ 2 + Real.pi ^ 2 - 3 * r - 5 * r * (Real.exp r)⁻¹ -
      2 * r * (Real.exp (2 * r))⁻¹ := by
  by_cases hr : r ≤ 0
  · have he : 0 < Real.exp r := Real.exp_pos r
    have he2 : 0 < Real.exp (2 * r) := Real.exp_pos (2 * r)
    have hp : 0 < r ^ 2 + Real.pi ^ 2 := by positivity
    have hri : 0 ≤ -3 * r := by linarith
    have h5 : 0 ≤ (-5 * r) * (Real.exp r)⁻¹ :=
      mul_nonneg (by nlinarith) (le_of_lt (inv_pos.mpr he))
    have h2 : 0 ≤ (-2 * r) * (Real.exp (2 * r))⁻¹ :=
      mul_nonneg (by nlinarith) (le_of_lt (inv_pos.mpr he2))
    nlinarith
  · have hr' : 0 ≤ r := le_of_not_ge hr
    have h1 : 0 < 1 + r := by linarith
    have h2 : 0 < 1 + 2 * r := by linarith
    have he : 0 < Real.exp r := Real.exp_pos r
    have he2 : 0 < Real.exp (2 * r) := Real.exp_pos (2 * r)
    have hE : 1 + r ≤ Real.exp r := by simpa [add_comm] using Real.add_one_le_exp r
    have hE2 : 1 + 2 * r ≤ Real.exp (2 * r) := by
      simpa [add_comm] using (Real.add_one_le_exp (2 * r))
    have hi : (Real.exp r)⁻¹ ≤ (1 + r)⁻¹ :=
      (inv_le_inv₀ he h1).2 hE
    have hi2 : (Real.exp (2 * r))⁻¹ ≤ (1 + 2 * r)⁻¹ :=
      (inv_le_inv₀ he2 h2).2 hE2
    have hfrac1 : 5 * r * (Real.exp r)⁻¹ ≤ 5 := by
      have hq : r / (1 + r) ≤ 1 := by
        apply (div_le_iff₀ h1).2
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hi hr'
      calc
        5 * r * (Real.exp r)⁻¹ = 5 * (r * (Real.exp r)⁻¹) := by ring
        _ ≤ 5 * (r * (1 + r)⁻¹) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 5 * (r / (1 + r)) := by rw [div_eq_mul_inv]
        _ ≤ 5 := by nlinarith [mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 5)]
    have hfrac2 : 2 * r * (Real.exp (2 * r))⁻¹ ≤ 1 := by
      have hq : (2 * r) / (1 + 2 * r) ≤ 1 := by
        apply (div_le_iff₀ h2).2
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hi2 hr'
      calc
        2 * r * (Real.exp (2 * r))⁻¹ = 2 * (r * (Real.exp (2 * r))⁻¹) := by ring
        _ ≤ 2 * (r * (1 + 2 * r)⁻¹) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * (r / (1 + 2 * r)) := by rw [div_eq_mul_inv]
        _ ≤ 1 := by simpa [div_eq_mul_inv, mul_assoc] using hq
    have hquad : 0 < r ^ 2 + Real.pi ^ 2 - 3 * r - 6 := by
      nlinarith [sq_nonneg (r - 3 / 2), Real.pi_gt_three]
    nlinarith

private lemma jfun_gap_formula (r : ℝ) :
    -2 * Real.exp r * deriv ell r - deriv jfun r =
      2 * (Real.exp r) ^ 3 / (1 + Real.exp r) ^ 3 *
        (r ^ 2 + Real.pi ^ 2 - 3 * r - 5 * r * (Real.exp r)⁻¹ -
          2 * r * (Real.exp (2 * r))⁻¹) := by
  rw [ell_deriv_formula, jfun_deriv_formula]
  have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have he2 : Real.exp (2 * r) ≠ 0 := (Real.exp_pos (2 * r)).ne'
  have hExp2 : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add]
    ring
  rw [hExp2]
  field_simp [he, he2]
  ring

theorem jfun_deriv_lt (r : ℝ) : deriv jfun r < -2 * Real.exp r * deriv ell r := by
  have hg := jfun_gap_formula r
  have hp : 0 < 2 * (Real.exp r) ^ 3 / (1 + Real.exp r) ^ 3 := by positivity
  have hb := jfun_gap_bracket_pos r
  have : 0 < -2 * Real.exp r * deriv ell r - deriv jfun r := by
    rw [hg]
    exact mul_pos hp hb
  linarith

end D5.S3.Quantum.PositiveResolvent
