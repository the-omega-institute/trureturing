/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredLeadingPair
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredLeadingPair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual filtered tail is a retained cosine with a strict exponent gap. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredExplicitFormula
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualProtectedZeroPair

/-! The leading conjugate pair in the compactly averaged Chebyshev log-tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators Classical ComplexConjugate Topology
open PositiveSpectralKernel (expMoment)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent (spectralExp)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredExplicitFormula
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualProtectedZeroPair

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair

private lemma norm_spectralExp (z : ℂ) (t : ℝ) :
    ‖spectralExp z t‖ = Real.exp ((z.re - 1) * t) := by
  simp only [spectralExp, Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma norm_actual_moment_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {h : ℝ} (hν : ν (Icc 0 h) = 1) (k : ℕ) :
    ‖expMoment ν (actualZero k - 1)‖ ≤ 1 := by
  have hsupport : ∀ᵐ s ∂ν, s ∈ Icc 0 h :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  have hz : (actualZero k).re < 1 :=
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  have hbound : ∀ᵐ s ∂ν, ‖spectralExp (actualZero k) s‖ ≤ 1 := by
    filter_upwards [hsupport] with s hs
    rw [norm_spectralExp, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz.le) hs.1
  change ‖∫ s : ℝ, spectralExp (actualZero k) s ∂ν‖ ≤ 1
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound

/-- The retained positive-ordinate zero and its conjugate give a cosine with the
multiplicity of the zero included. The minus sign comes from the Chebyshev
log-tail formula. All remaining terms, including the signed correction, satisfy
the bound at the cutoff exponent `b - 1`. -/
theorem actual_filtered_leading_pair (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (k₀ : ℕ) {h b : ℝ} (hν : ν (Icc 0 h) = 1) (hb₀ : 0 ≤ b)
    (hb : b < (actualZero k₀).re) (hγ : 0 < (actualZero k₀).im)
    (hmoment : expMoment ν (actualZero k₀ - 1) ≠ 0)
    (hkill : ∀ k : ℕ, b < (actualZero k).re → actualZero k ≠ actualZero k₀ →
      actualZero k ≠ conj (actualZero k₀) → expMoment ν (actualZero k - 1) = 0) :
    let ρ := actualZero k₀
    let a := actualCoeff k₀ * expMoment ν (ρ - 1)
    let C : ℝ := 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖a‖
    let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
    a ≠ 0 ∧ 0 < C ∧ b - 1 < ρ.re - 1 ∧ 0 ≤ E ∧
      ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
        (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
          -(C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + a.arg)) + R t ∧
        |R t| ≤ E * Real.exp ((b - 1) * t) := by
  let ρ := actualZero k₀
  let a := actualCoeff k₀ * expMoment ν (ρ - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖a‖
  let M : ℝ := ∑' k : ℕ, ‖actualCoeff k‖
  let L : ℝ := Real.log (2 * Real.pi)
  let leading (t : ℝ) : ℝ :=
    C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + a.arg)
  let mode (t : ℝ) (k : ℕ) : ℂ :=
    actualCoeff k * expMoment ν (actualZero k - 1) * spectralExp (actualZero k) t
  let rest (t : ℝ) (k : ℕ) : ℂ :=
    if actualZero k = ρ ∨ actualZero k = conj ρ then 0 else mode t k
  let R (t : ℝ) : ℝ := -(∑' k : ℕ, rest t k).re + averagedActualCorrection ν t
  have hpair : 0 < C ∧ ∀ t : ℝ,
      HasSum (fun k : ℕ =>
        if actualZero k = ρ ∨ actualZero k = conj ρ then mode t k else 0)
        (leading t : ℂ) :=
    actual_protected_pair_hasSum ν k₀ hγ hmoment
  have ha : a ≠ 0 := by
    intro hz
    have hC : (0 : ℝ) < 0 := by
      simpa only [C, hz, norm_zero, mul_zero] using hpair.1
    exact (lt_irrefl 0) hC
  have hM : 0 ≤ M := tsum_nonneg (fun _ => norm_nonneg _)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨ha, hpair.1, sub_lt_sub_right hb 1, add_nonneg hM hL, R, ?_⟩
  intro t ht
  have ht₀ : 0 ≤ t := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans ht
  have hfull : HasSum (mode t) (∑' k : ℕ, mode t k) :=
    (actual_filtered_spectral_hasSum ν hν ht₀).summable.hasSum
  have hrest : HasSum (rest t) ((∑' k : ℕ, mode t k) - (leading t : ℂ)) := by
    refine (hfull.sub (hpair.2 t)).congr_fun ?_
    intro k
    by_cases hk : actualZero k = ρ ∨ actualZero k = conj ρ <;> simp [rest, hk]
  constructor
  · have hsplit : (∑' k : ℕ, mode t k) = (leading t : ℂ) + ∑' k : ℕ, rest t k := by
      rw [hrest.tsum_eq]
      abel
    have hformula : (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
        -(∑' k : ℕ, mode t k).re + averagedActualCorrection ν t :=
      actual_filtered_explicit_formula ν hν ht
    change (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) = -leading t + R t
    rw [hformula, hsplit, Complex.add_re, Complex.ofReal_re]
    dsimp only [R]
    abel
  · have hbound (k : ℕ) : ‖rest t k‖ ≤ ‖actualCoeff k‖ * Real.exp ((b - 1) * t) := by
      have hnonneg := mul_nonneg (norm_nonneg (actualCoeff k))
        (Real.exp_nonneg ((b - 1) * t))
      by_cases hk : actualZero k = ρ ∨ actualZero k = conj ρ
      · simpa only [rest, if_pos hk, norm_zero] using hnonneg
      · simp only [rest, if_neg hk]
        by_cases hkb : (actualZero k).re ≤ b
        · have hdecay : ‖spectralExp (actualZero k) t‖ ≤ Real.exp ((b - 1) * t) := by
            rw [norm_spectralExp]
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (sub_le_sub_right hkb 1) ht₀)
          have hcoeff : ‖actualCoeff k‖ * ‖expMoment ν (actualZero k - 1)‖ ≤
              ‖actualCoeff k‖ :=
            mul_le_of_le_one_right (norm_nonneg _) (norm_actual_moment_le_one ν hν k)
          simp only [mode, norm_mul]
          exact mul_le_mul hcoeff hdecay (norm_nonneg _) (norm_nonneg _)
        · obtain ⟨hρ, hconj⟩ := not_or.mp hk
          have hz := hkill k (lt_of_not_ge hkb) hρ hconj
          simpa only [mode, hz, mul_zero, zero_mul, norm_zero] using hnonneg
    have hmajorant : HasSum (fun k : ℕ => ‖actualCoeff k‖ * Real.exp ((b - 1) * t))
        (M * Real.exp ((b - 1) * t)) :=
      actualCoeff_hasSum.summable.norm.hasSum.mul_right _
    have hseries : ‖∑' k : ℕ, rest t k‖ ≤ M * Real.exp ((b - 1) * t) :=
      hrest.summable.hasSum.norm_le_of_bounded hmajorant hbound
    obtain ⟨hlower, hupper⟩ := averagedActualCorrection_bounds ν hν ht₀
    have hcorr : |averagedActualCorrection ν t| ≤ L * Real.exp (-t) := by
      rw [abs_of_nonpos hupper]
      exact neg_le_of_neg_le hlower
    have hdecay : Real.exp (-t) ≤ Real.exp ((b - 1) * t) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hb₀ ht₀])
    calc
      |R t| ≤ |(∑' k : ℕ, rest t k).re| + |averagedActualCorrection ν t| := by
        simpa only [R, abs_neg] using
          (abs_add_le (-(∑' k : ℕ, rest t k).re) (averagedActualCorrection ν t))
      _ ≤ M * Real.exp ((b - 1) * t) + L * Real.exp ((b - 1) * t) :=
        add_le_add ((Complex.abs_re_le_norm _).trans hseries)
          (hcorr.trans (mul_le_mul_of_nonneg_left hdecay hL))
      _ = (M + L) * Real.exp ((b - 1) * t) := (add_mul _ _ _).symm

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair
