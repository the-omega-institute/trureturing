/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualZeroLaplace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolutely convergent Laplace transform over all actual analytic zero occurrences. -/
/- Complete actual-occurrence Laplace source candidate; final admission pending.
   Complete actual zero occurrence family; no abstract mass or symmetry premise.
   Reuses the same normalized xi-resolvent calculation already consumed inside
   ActualReciprocalSquareBounds.actual_pairWeight_hasSum, then transports every
   analytic multiplicity to the existing actualZero natural presentation.
   Native evidence is recorded separately. No RH claim is made. -/

import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import Mathlib.Logic.Equiv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import D5.S3.Weil.ZetaExplicit.XiLogDeriv
import D5.S3.Weil.ZetaExplicit.GammaRBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Resolvent.XiNormalizedResolvent
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit

/-- Exact mass, conjugation, convergence, bound and absolute weighted exchange,
rederived from the actual normalized xi resolvent. The proof below is the
sealed source4564 argument with native elaboration repairs, not an analytic premise. -/
theorem actual_complete_H_package :
    let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
    HasSum a (firstLiMass : ℂ) ∧
      ∃ c : Equiv.Perm ℕ,
        (∀ k : ℕ, actualZero (c k) = conj (actualZero k)) ∧
        (∀ y : ℝ,
          Summable (fun k : ℕ => a k * Complex.exp ((y : ℂ) * actualZero k)) ∧
          (∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)).im = 0 ∧
          ‖∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
            ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0)) ∧
        (∀ w : ℝ → ℂ, AEStronglyMeasurable w volume →
          Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖) →
          HasSum
            (fun k : ℕ => a k * ∫ y : ℝ,
              Complex.exp ((y : ℂ) * actualZero k) * w y)
            (∫ y : ℝ,
              (∑' k : ℕ, a k * Complex.exp ((y : ℂ) * actualZero k)) * w y)) := by
  classical
  dsimp only
  let a : ℕ → ℂ := fun k => 1 / (actualZero k * (1 - actualZero k))
  have hx1 : xiReading 1 ≠ 0 := by
    rw [xi_reading_endpoint_values.2]
    norm_num
  have hres := xi_reading_normalized_resolvent_hasSum actualData 1 hx1
  have href : logDeriv xiReading 0 = -logDeriv xiReading 1 := by
    simpa only [sub_self] using xi_logDeriv_reflection (1 : ℂ)
  have hend : logDeriv xiReading 1 =
      ((1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    change deriv xiReading 1 / xiReading 1 = _
    exact first_li_coefficient_normalization.1
  have hweighted : HasSum
      (fun n : ℕ => (actualData.multiplicity n : ℂ) *
        (1 / (actualData.zero n * (1 - actualData.zero n))))
      (firstLiMass : ℂ) := by
    convert hres using 1
    · funext n
      have hs := (actualData.zero_isNontrivial n).2
      have h0 : actualData.zero n ≠ 0 := by
        intro he
        have := hs.1
        simpa only [he, Complex.zero_re, lt_self_iff_false] using this
      have h1 : actualData.zero n ≠ 1 := by
        intro he
        have := hs.2
        simpa only [he, Complex.one_re, lt_self_iff_false] using this
      field_simp [h0, sub_ne_zero.mpr h1.symm]
      <;> ring
    · rw [href, hend]
      unfold firstLiMass
      push_cast
      ring
  have hnorm : Summable (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      ‖1 / (actualData.zero n * (1 - actualData.zero n))‖) := by
    simpa [norm_mul] using hweighted.summable.norm
  have hSigmaNorm : Summable (fun p : ActualZeroOccurrence =>
      ‖1 / (actualData.zero p.1 * (1 - actualData.zero p.1))‖) := by
    apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using hnorm
  have hSigma : Summable (fun p : ActualZeroOccurrence =>
      1 / (actualData.zero p.1 * (1 - actualData.zero p.1))) :=
    hSigmaNorm.of_norm
  have hSigmaMass : HasSum (fun p : ActualZeroOccurrence =>
      1 / (actualData.zero p.1 * (1 - actualData.zero p.1))) (firstLiMass : ℂ) := by
    convert hSigma.hasSum using 1
    rw [hSigma.tsum_sigma]
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hweighted.tsum_eq.symm
  have hmass : HasSum a (firstLiMass : ℂ) := by
    simpa only [Function.comp_def, a, actualZero] using
      (actualOccurrenceEquiv.hasSum_iff).2 hSigmaMass
  have hRSigma : Summable (fun p : ActualZeroOccurrence =>
      ((actualData.zero p.1).im)⁻¹ ^ 2) := by
    apply (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using actual_weighted_inverse_square_summable
  have hR : Summable (fun k : ℕ => ((actualZero k).im)⁻¹ ^ 2) := by
    simpa only [Function.comp_def, actualZero] using
      (actualOccurrenceEquiv.summable_iff).2 hRSigma
  have hcoeff (k : ℕ) : ‖a k‖ ≤ ((actualZero k).im)⁻¹ ^ 2 := by
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
    have hprod : (actualZero k).im ^ 2 ≤ ‖actualZero k‖ * ‖1 - actualZero k‖ := by
      calc
        _ = |(actualZero k).im| * |(actualZero k).im| := by
          rw [← sq_abs]
          ring
        _ ≤ _ := mul_le_mul hp hm (abs_nonneg _) (norm_nonneg _)
    calc
      ‖a k‖ = 1 / (‖actualZero k‖ * ‖1 - actualZero k‖) := by
        simp only [a, norm_div, norm_one, norm_mul]
      _ ≤ 1 / ((actualZero k).im ^ 2) := one_div_le_one_div_of_le ht2 hprod
      _ = ((actualZero k).im)⁻¹ ^ 2 := by simp only [one_div, inv_pow]
  let σ : Equiv.Perm ActualZeroOccurrence :=
    Equiv.sigmaCongr actualData.conjugation
      (fun n => finCongr (actualData.multiplicity_conjugation n).symm)
  let c : Equiv.Perm ℕ :=
    actualOccurrenceEquiv.trans (σ.trans actualOccurrenceEquiv.symm)
  have hc (k : ℕ) : actualZero (c k) = conj (actualZero k) := by
    simp only [actualZero, c, Equiv.trans_apply, Equiv.apply_symm_apply]
    change actualData.zero (actualData.conjugation (actualOccurrenceEquiv k).1) = _
    exact actualData.zero_conjugation _
  let f : ℝ → ℕ → ℂ := fun y k => a k * Complex.exp ((y : ℂ) * actualZero k)
  have hdom (y : ℝ) (k : ℕ) : ‖f y k‖ ≤ ‖a k‖ * Real.exp (max y 0) := by
    have hs := (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2
    have hs0 : 0 ≤ (actualZero k).re := hs.1.le
    have hs1 : (actualZero k).re ≤ 1 := hs.2.le
    have he : y * (actualZero k).re ≤ max y 0 := by
      rcases le_or_gt 0 y with hy | hy
      · rw [max_eq_left hy]
        nlinarith
      · have hm : y * (actualZero k).re ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hy.le hs0
        simpa only [max_eq_right hy.le] using hm
    dsimp only [f]
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
  have hsum (y : ℝ) : Summable (f y) :=
    Summable.of_norm_bounded (hmass.summable.norm.mul_right (Real.exp (max y 0)))
      (hdom y)
  have hconj (y : ℝ) (k : ℕ) : conj (f y k) = f y (c k) := by
    simp [f, a, hc, ← Complex.exp_conj]
  have hreal (y : ℝ) : (∑' k : ℕ, f y k).im = 0 := by
    have he : conj (∑' k : ℕ, f y k) = ∑' k : ℕ, f y k := by
      rw [Complex.conj_tsum]
      simp_rw [hconj]
      exact c.tsum_eq (f y)
    have him := congrArg Complex.im he
    simp only [Complex.conj_im] at him
    linarith
  have hbound (y : ℝ) : ‖∑' k : ℕ, f y k‖ ≤
      ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0) := by
    have hmajor : HasSum
        (fun k : ℕ => (((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0))
        ((∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0)) :=
      hR.hasSum.mul_right _
    calc
      _ ≤ (∑' k : ℕ, ((actualZero k).im)⁻¹ ^ 2) * Real.exp (max y 0) := by
        apply tsum_of_norm_bounded hmajor
        intro k
        exact (hdom y k).trans
          (mul_le_mul_of_nonneg_right (hcoeff k) (Real.exp_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_right actual_inverse_square_mass_le_height
        (Real.exp_nonneg _)
  have hexchange (w : ℝ → ℂ) (hw : AEStronglyMeasurable w volume)
      (hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖)) :
      HasSum
        (fun k : ℕ => a k * ∫ y : ℝ,
          Complex.exp ((y : ℂ) * actualZero k) * w y)
        (∫ y : ℝ, (∑' k : ℕ, f y k) * w y) := by
    let F : ℕ → ℝ → ℂ := fun k y => f y k * w y
    let b : ℕ → ℝ → ℝ := fun k y =>
      ‖a k‖ * (Real.exp (max y 0) * ‖w y‖)
    have hF : ∀ k : ℕ, AEStronglyMeasurable (F k) volume := by
      intro k
      have hcontinuous : Continuous (fun y : ℝ => f y k) := by
        dsimp only [f]
        fun_prop
      exact hcontinuous.aestronglyMeasurable.mul hw
    have hFb : ∀ k : ℕ, ∀ᵐ y : ℝ, ‖F k y‖ ≤ b k y := by
      intro k
      exact ae_of_all volume fun y => by
        calc
          _ = ‖f y k‖ * ‖w y‖ := norm_mul _ _
          _ ≤ (‖a k‖ * Real.exp (max y 0)) * ‖w y‖ :=
            mul_le_mul_of_nonneg_right (hdom y k) (norm_nonneg _)
          _ = _ := by dsimp only [b]; ring
    have hbsum : ∀ᵐ y : ℝ, Summable (fun k : ℕ => b k y) :=
      ae_of_all volume fun y =>
        hmass.summable.norm.mul_right (Real.exp (max y 0) * ‖w y‖)
    have hbint : Integrable (fun y : ℝ => ∑' k : ℕ, b k y) := by
      simpa only [b, tsum_mul_right] using
        hwi.const_mul (∑' k : ℕ, ‖a k‖)
    have hlim : ∀ᵐ y : ℝ,
        HasSum (fun k : ℕ => F k y) ((∑' k : ℕ, f y k) * w y) := by
      exact ae_of_all volume fun y => (hsum y).hasSum.mul_right (w y)
    have hd := hasSum_integral_of_dominated_convergence b hF hFb hbsum hbint hlim
    convert hd using 1
    funext k
    dsimp only [F, f]
    simp only [mul_assoc, integral_const_mul]
  exact ⟨hmass, c, hc, (fun y => ⟨hsum y, hreal y, hbound y⟩), hexchange⟩

/-- Each natural index is an occurrence, including the analytic multiplicity. -/
def actualCoeff (k : ℕ) : ℂ := 1 / (actualZero k * (1 - actualZero k))

/-- Complete zero series on the full real axis. -/
def actualH (y : ℝ) : ℂ :=
  ∑' k : ℕ, actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)

theorem actualCoeff_hasSum : HasSum actualCoeff (firstLiMass : ℂ) :=
  actual_complete_H_package.1

theorem actualH_summable (y : ℝ) :
    Summable (fun k : ℕ => actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)) :=
  actual_complete_H_package.2.choose_spec.2.1 y |>.1

theorem actualH_im (y : ℝ) : (actualH y).im = 0 :=
  actual_complete_H_package.2.choose_spec.2.1 y |>.2.1

theorem actualH_bound (y : ℝ) :
    ‖actualH y‖ ≤ ((101 / 100 : ℝ) * firstLiMass) * Real.exp (max y 0) :=
  actual_complete_H_package.2.choose_spec.2.1 y |>.2.2

private theorem actual_zero_strip (k : ℕ) :
    0 < (actualZero k).re ∧ (actualZero k).re < 1 :=
  (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2

private theorem term_bound (y : ℝ) (k : ℕ) :
    ‖actualCoeff k * Complex.exp ((y : ℂ) * actualZero k)‖ ≤
      ‖actualCoeff k‖ * Real.exp (max y 0) := by
  obtain ⟨h0, h1⟩ := actual_zero_strip k
  have he : y * (actualZero k).re ≤ max y 0 := by
    rcases le_or_gt 0 y with hy | hy
    · rw [max_eq_left hy]
      nlinarith
    · rw [max_eq_right hy.le]
      exact mul_nonpos_of_nonpos_of_nonneg hy.le h0.le
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)

theorem actualH_continuous : Continuous actualH := by
  rw [continuous_iff_continuousAt]
  intro y
  let u : ℕ → ℝ := fun k => ‖actualCoeff k‖ * Real.exp (max (y + 1) 0)
  have hu : Summable u := actualCoeff_hasSum.summable.norm.mul_right _
  have hc : ContinuousOn actualH (Set.Iio (y + 1)) := by
    apply continuousOn_tsum
      (fun k => (show Continuous (fun x : ℝ =>
        actualCoeff k * Complex.exp ((x : ℂ) * actualZero k)) by fun_prop).continuousOn)
      hu
    intro k x hx
    exact (term_bound x k).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (max_le_max hx.le le_rfl)) (norm_nonneg _))
  exact hc.continuousAt (isOpen_Iio.mem_nhds (by simp))

/-- Finite analytic-order fibers are transported without deleting occurrences. -/
private theorem occurrence_hasSum {f : ℂ → ℂ} {z : ℂ}
    (h : HasSum (fun n : ℕ => (actualData.multiplicity n : ℂ) *
      f (actualData.zero n)) z) :
    HasSum (fun k : ℕ => f (actualZero k)) z := by
  have hn : Summable (fun n : ℕ => (actualData.multiplicity n : ℝ) *
      ‖f (actualData.zero n)‖) := by
    simpa only [norm_mul, Complex.norm_natCast] using h.summable.norm
  have hp : Summable (fun p : ActualZeroOccurrence => ‖f (actualData.zero p.1)‖) := by
    apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using hn
  have hs := hp.of_norm
  have he : HasSum (fun p : ActualZeroOccurrence => f (actualData.zero p.1)) z := by
    convert hs.hasSum using 1
    rw [hs.tsum_sigma]
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using h.tsum_eq.symm
  simpa only [Function.comp_def, actualZero] using
    (actualOccurrenceEquiv.hasSum_iff).2 he

theorem xiReading_ne_zero_right {s : ℂ} (hs : 1 < s.re) : xiReading s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  rw [xi_reading_eq_completed_zeta hs0 hs1, completedZetaReading,
    (Zeta23.WeilEF.completedZeta_eventuallyEq_mul (by linarith : 0 < s.re)).eq_of_nhds]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0)
    (sub_ne_zero.mpr hs1)) (mul_ne_zero
      (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
      (riemannZeta_ne_zero_of_one_lt_re hs))

theorem xi_logDeriv_zero : logDeriv xiReading 0 = -(firstLiMass : ℂ) / 2 := by
  have hr : logDeriv xiReading 0 = -logDeriv xiReading 1 := by
    simpa only [sub_self] using xi_logDeriv_reflection (1 : ℂ)
  have hend : logDeriv xiReading 1 =
      ((1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) :=
    first_li_coefficient_normalization.1
  rw [hr, hend]
  unfold firstLiMass
  push_cast
  ring

/-- The normalized, convergent resolvent is never split into reciprocal-zero sums. -/
theorem actual_normalized_resolvent {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (s - actualZero k) + 1 / actualZero k)
      (logDeriv xiReading s + (firstLiMass : ℂ) / 2) := by
  have h := occurrence_hasSum (f := fun z : ℂ => 1 / (s - z) + 1 / z)
    (xi_reading_normalized_resolvent_hasSum actualData s (xiReading_ne_zero_right hs))
  simpa only [xi_logDeriv_zero, neg_div, sub_neg_eq_add] using h

/-- Exact bridge from the actual normalized resolvent to the integrated coefficients. -/
theorem actual_resolvent_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => actualCoeff k / (s - actualZero k))
      (((firstLiMass : ℂ) * (s - 1 / 2) - logDeriv xiReading s) / (s * (s - 1))) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s - 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h := ((actualCoeff_hasSum.mul_left s).sub
    (actual_normalized_resolvent hs)).mul_right (s * (s - 1))⁻¹
  convert h using 1
  · funext k
    obtain ⟨h0, h1⟩ := actual_zero_strip k
    have hr0 : actualZero k ≠ 0 := by intro e; simpa [e] using h0
    have hr1 : 1 - actualZero k ≠ 0 := by
      intro e
      have := congrArg Complex.re e
      simp at this
      linarith
    have hsr : s - actualZero k ≠ 0 := by
      intro e
      have := congrArg Complex.re e
      simp at this
      linarith
    dsimp only [actualCoeff]
    field_simp [hr0, hr1, hsr, hs0, hs1]
    <;> ring
  · ring

/-- Genuine half-line norm integrability from the actual strip and absolute mass. -/
theorem actualH_laplace_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * actualH y) (Set.Ioi 0) := by
  have hb : IntegrableOn (fun y : ℝ =>
      ((101 / 100 : ℝ) * firstLiMass) * Real.exp ((1 - s.re) * y)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : 1 - s.re < 0) 0).const_mul _
  refine hb.mono' (by
    exact ((show Continuous (fun y : ℝ => Complex.exp (-s * y)) by fun_prop).mul
      actualH_continuous).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  calc
    ‖Complex.exp (-s * y) * actualH y‖ = Real.exp (-s.re * y) * ‖actualH y‖ := by
      simp [norm_mul, Complex.norm_exp]
    _ ≤ Real.exp (-s.re * y) *
        (((101 / 100 : ℝ) * firstLiMass) * Real.exp y) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [max_eq_left (le_of_lt (show 0 < y from hy))] using actualH_bound y) (Real.exp_nonneg _)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2 <;> ring

/-- Exact Laplace identity for the complete actual occurrence family. The weighted
exchange is the proved absolute dominated-convergence statement in the package. -/
theorem actualH_laplace {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Set.Ioi 0, Complex.exp (-s * y) * actualH y) =
      (((firstLiMass : ℂ) * (s - 1 / 2) - logDeriv xiReading s) / (s * (s - 1))) := by
  classical
  let w : ℝ → ℂ := (Set.Ioi (0 : ℝ)).indicator (fun y => Complex.exp (-s * y))
  have hw : AEStronglyMeasurable w volume :=
    (show Continuous (fun y : ℝ => Complex.exp (-s * y)) by fun_prop).aestronglyMeasurable
      |>.indicator measurableSet_Ioi
  have hwi : Integrable (fun y : ℝ => Real.exp (max y 0) * ‖w y‖) := by
    have he : (fun y : ℝ => Real.exp (max y 0) * ‖w y‖) =
        (Set.Ioi (0 : ℝ)).indicator (fun y => Real.exp ((1 - s.re) * y)) := by
      funext y
      by_cases hy : y ∈ Set.Ioi (0 : ℝ)
      · simp only [w, Set.indicator_of_mem hy, max_eq_left (le_of_lt (show 0 < y from hy)), Complex.norm_exp]
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        rw [← Real.exp_add]
        congr 1
        ring
      · simp only [w, Set.indicator_of_notMem hy, norm_zero, mul_zero]
    rw [he, integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith : 1 - s.re < 0) 0
  have hx := actual_complete_H_package.2.choose_spec.2.2 w hw hwi
  have hterm (k : ℕ) :
      (∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) * w y) =
        1 / (s - actualZero k) := by
    have he : (fun y : ℝ => Complex.exp ((y : ℂ) * actualZero k) * w y) =
        (Set.Ioi (0 : ℝ)).indicator
          (fun y => Complex.exp ((actualZero k - s) * y)) := by
      funext y
      by_cases hy : y ∈ Set.Ioi (0 : ℝ)
      · simp only [w, Set.indicator_of_mem hy, ← Complex.exp_add]
        congr 1
        ring
      · simp only [w, Set.indicator_of_notMem hy, mul_zero]
    rw [he, integral_indicator measurableSet_Ioi,
      integral_exp_mul_complex_Ioi (by
        simp only [Complex.sub_re]
        linarith [(actual_zero_strip k).2])]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show actualZero k - s = -(s - actualZero k) by ring, div_neg]
    simp only [neg_neg, neg_div, one_div]
  have htotal : (∫ y : ℝ, actualH y * w y) =
      ∫ y : ℝ in Set.Ioi 0, Complex.exp (-s * y) * actualH y := by
    have he : (fun y : ℝ => actualH y * w y) =
        (Set.Ioi (0 : ℝ)).indicator (fun y => Complex.exp (-s * y) * actualH y) := by
      funext y
      by_cases hy : y ∈ Set.Ioi (0 : ℝ) <;> simp [w, hy, mul_comm]
    rw [he, integral_indicator measurableSet_Ioi]
  change HasSum (fun k : ℕ => actualCoeff k *
    ∫ y : ℝ, Complex.exp ((y : ℂ) * actualZero k) * w y)
    (∫ y : ℝ, actualH y * w y) at hx
  simp_rw [hterm] at hx
  rw [htotal] at hx
  have hx' : HasSum (fun k : ℕ => actualCoeff k / (s - actualZero k))
      (∫ y : ℝ in Set.Ioi 0, Complex.exp (-s * y) * actualH y) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using hx
  exact hx'.unique (actual_resolvent_hasSum hs)

/-- Product differentiation with all nonvanishing obligations paid in Re(s)>1. -/
theorem xi_logDeriv_right {s : ℂ} (hs : 1 < s.re) :
    logDeriv xiReading s = 1 / s + 1 / (s - 1) -
      (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2 +
        deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; norm_num at hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  have hc : completedRiemannZeta s ≠ 0 := by
    rw [(Zeta23.WeilEF.completedZeta_eventuallyEq_mul
      (by linarith : 0 < s.re)).eq_of_nhds]
    exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)) hζ
  have hnear : xiReading =ᶠ[𝓝 s]
      (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1) * completedRiemannZeta z)) := by
    filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
    rw [xi_reading_eq_completed_zeta hz0 hz1, completedZetaReading]
    ring
  have heq : logDeriv xiReading s = logDeriv
      (fun z : ℂ => (1 / 2 : ℂ) * (z * (z - 1) * completedRiemannZeta z)) s := by
    rw [logDeriv_apply, logDeriv_apply, hnear.deriv_eq, hnear.eq_of_nhds]
  rw [heq, logDeriv_const_mul _ _ (by norm_num),
    logDeriv_fun_mul (f := fun z : ℂ => z * (z - 1))
      (g := completedRiemannZeta) s (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hc (by fun_prop)
      (differentiableAt_completedZeta hs0 hs1),
    logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1)
      s hs0 (sub_ne_zero.mpr hs1) (by fun_prop) (by fun_prop),
    Zeta23.WeilEF.logDeriv_completedZeta s hs1 hζ (by linarith),
    Zeta23.WeilEF.logDeriv_Gammaℝ (by linarith)]
  simp only [logDeriv_apply, deriv_id'', deriv_sub_const, one_div]
  ring

end D5.S3.Weil.Mertens.IntegratedExplicit
end


