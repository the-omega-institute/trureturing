/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/RHActualHSqrtBound
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/RHActualHSqrtBound
   mirror-E: none(waiver:conditional-rh-consumer)
   anchors: []
   utility: none
   digest: RH moves the actual integrated zero Laplace series from the unconditional exp(max y 0) envelope to the genuine square-root envelope exp(y/2). -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualZeroLaplace
import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Zeros.Endpoints.FirstLiCoefficientPositivity
open Filter
open scoped BigOperators ComplexConjugate Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit

/-!
The existing actual Laplace package bounds each coefficient by the complete
inverse-square ordinate mass.  Under RH every actual zero has real part one
half, so the same summable majorant carries `exp (y / 2)` rather than the
unconditional `exp (max y 0)`.  The factor `101/100` is the already verified
height refinement; no abstract zero family or bind-only hypothesis is added.
-/
private theorem actualH_sqrt_bound_of_rh (hRH : RiemannHypothesis) (y : ℝ) :
    ‖actualH y‖ ≤
      (101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2) := by
  have hSigma : Summable (fun p : ActualZeroOccurrence =>
      ((actualData.zero p.1).im)⁻¹ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using
      actual_weighted_inverse_square_summable
  have hR : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      (actualOccurrenceEquiv.summable_iff).2 hSigma
  have hcoeff (k : ℕ) : ‖actualCoeff k‖ ≤ ((actualZero k).im)⁻¹ ^ 2 := by
    have hheight := actual_height_gt_ten (actualZero k)
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)
    have ht : 0 < |(actualZero k).im| := by linarith
    have ht2 : 0 < (actualZero k).im ^ 2 := by
      have he := sq_pos_of_pos ht
      simpa only [sq_abs] using he
    have hp : |(actualZero k).im| ≤ ‖actualZero k‖ :=
      Complex.abs_im_le_norm _
    have hm : |(actualZero k).im| ≤ ‖1 - actualZero k‖ := by
      simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
        Complex.abs_im_le_norm (1 - actualZero k)
    have hprod : (actualZero k).im ^ 2 ≤
        ‖actualZero k‖ * ‖1 - actualZero k‖ := by
      calc
        _ = |(actualZero k).im| * |(actualZero k).im| := by
          rw [← sq_abs]
          ring
        _ ≤ _ := mul_le_mul hp hm (abs_nonneg _) (norm_nonneg _)
    calc
      ‖actualCoeff k‖ =
          1 / (‖actualZero k‖ * ‖1 - actualZero k‖) := by
        simp only [actualCoeff, norm_div, norm_one, norm_mul]
      _ ≤ 1 / ((actualZero k).im ^ 2) :=
        one_div_le_one_div_of_le ht2 hprod
      _ = ((actualZero k).im)⁻¹ ^ 2 := by
        simp only [one_div, inv_pow]
  have hline (k : ℕ) : (actualZero k).re = (1 : ℝ) / 2 := by
    simpa only [actualZero, D5.S3.Weil.Convention.criticalAbscissa] using
      zeroData_zero_on_critical_line_of_rh hRH actualData
        (actualOccurrenceEquiv k).1
  have hterm (k : ℕ) :
      ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ((actualZero k).im)⁻¹ ^ 2 * Real.exp (y / 2) := by
    have hre : ((y : ℂ) * actualZero k).re = y / 2 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hline k]
      ring
    rw [norm_mul, Complex.norm_exp, hre]
    exact mul_le_mul_of_nonneg_right (hcoeff k) (Real.exp_nonneg _)
  have hmajor : HasSum
      (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2 * Real.exp (y / 2))
      ((∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (y / 2)) :=
    hR.hasSum.mul_right _
  calc
    ‖actualH y‖ =
        ‖∑' k : ℕ, actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ := rfl
    _ ≤ (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (y / 2) := by
      exact tsum_of_norm_bounded hmajor hterm
    _ ≤ (101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2) := by
      exact mul_le_mul_of_nonneg_right
        actual_inverse_square_mass_le_height (Real.exp_nonneg _)

/-! The registration-facing source theorem keeps the witness equality in the
law's telescope, so the extracted readout is source-aligned without a
synthetic parameter in the mirror. -/
theorem actualH_sqrt_bound_of_rh_registered :
    actualH 0 = actualH 0 ∧
      ∀ hRH : RiemannHypothesis, ∀ y : ℝ,
        ‖actualH y‖ ≤
          (101 / 100 : ℝ) * firstLiMass * Real.exp (y / 2) := by
  constructor
  · rfl
  · intro hRH y
    exact actualH_sqrt_bound_of_rh hRH y

private theorem actualH_tendsto_atBot :
    Tendsto actualH atBot (𝓝 (0 : ℂ)) := by
  have hmajor : Summable (fun k : ℕ => ‖actualCoeff k‖) :=
    actualCoeff_hasSum.summable.norm
  have hterm (k : ℕ) :
      Tendsto (fun y : ℝ => actualCoeff k *
        Complex.exp ((y : ℂ) * actualZero k)) atBot (𝓝 (0 : ℂ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hre : 0 < (actualZero k).re :=
      (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.1
    have harg : Tendsto (fun y : ℝ => y * (actualZero k).re)
        atBot atBot := by
      simpa only [mul_comm] using
        ((tendsto_const_mul_atBot_of_pos hre).2 tendsto_id :
          Tendsto (fun y : ℝ => (actualZero k).re * y) atBot atBot)
    have hexp : Tendsto (fun y : ℝ =>
        Real.exp (y * (actualZero k).re)) atBot (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have hnorm : Tendsto (fun y : ℝ =>
        ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖)
        atBot (𝓝 0) := by
      simpa [norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using (hexp.const_mul ‖actualCoeff k‖)
    exact hnorm
  have hbound : ∀ᶠ y : ℝ in atBot, ∀ k : ℕ,
      ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
        ‖actualCoeff k‖ := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with y hy k
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_le_of_le_one_right (norm_nonneg _) <| by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg hy
        (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.1.le
  change Tendsto (fun y : ℝ => ∑' k : ℕ,
      actualCoeff k * Complex.exp ((y : ℂ) * actualZero k))
      atBot (𝓝 (0 : ℂ))
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence hmajor hterm hbound)

private theorem actualH_zero : actualH 0 = (firstLiMass : ℂ) := by
  simpa [actualH] using actualCoeff_hasSum.tsum_eq

theorem actualH_nonconstant : ∃ y : ℝ, actualH y ≠ actualH 0 := by
  have hmass_pos : 0 < firstLiMass := by
    unfold firstLiMass
    linarith [first_li_coefficient_pos]
  have hmass_ne : (firstLiMass : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hmass_pos)
  by_contra h
  have hall : ∀ y : ℝ, actualH y = actualH 0 := by
    intro y
    by_contra hy
    exact h ⟨y, hy⟩
  have hzero : Tendsto (fun _ : ℝ => actualH 0) atBot (𝓝 (0 : ℂ)) :=
    actualH_tendsto_atBot.congr' (Eventually.of_forall fun y => hall y)
  have heq : actualH 0 = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hzero
  apply hmass_ne
  calc
    (firstLiMass : ℂ) = actualH 0 := actualH_zero.symm
    _ = 0 := heq

#print axioms actualH_sqrt_bound_of_rh
#print axioms actualH_sqrt_bound_of_rh_registered
#print axioms actualH_nonconstant

end D5.S3.Weil.Mertens.IntegratedExplicit
