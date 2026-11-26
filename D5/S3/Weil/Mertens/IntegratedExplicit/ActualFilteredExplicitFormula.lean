/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredExplicitFormula
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualFilteredExplicitFormula
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual integrated Chebyshev formula commutes with compact probability averaging. -/

import D5.S3.Analytic.Asymptotics.PositiveSpectralKernel
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Compact probability averages of the complete Chebyshev log-tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators Topology
open PositiveSpectralKernel (expMoment)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent (spectralExp)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredExplicitFormula

private def correction (v : ℝ) : ℝ :=
  (trivialT v - Real.log (2 * Real.pi)) * Real.exp (-v)

/-- Average of the signed trivial-zero and constant terms in the actual formula. -/
def averagedActualCorrection (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ s, correction (t + s) ∂ν

private lemma ae_nonneg_shift (ν : Measure ℝ) [IsProbabilityMeasure ν] {h : ℝ}
    (hν : ν (Icc 0 h) = 1) : ∀ᵐ s ∂ν, 0 ≤ s := by
  have hsupport : ∀ᵐ s ∂ν, s ∈ Icc 0 h :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  exact hsupport.mono fun _ hs => hs.1

-- The pointwise calculation in ActualSignedGaussianEndpoint, in terms of actualH.
private lemma q_exp_eq {v : ℝ} (hv : Real.log 2 ≤ v) :
    Q (Real.exp v) = -(actualH v * (Real.exp (-v) : ℂ)).re + correction v := by
  have hv₀ : 0 < v := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hv
  have hendpoint : 2 ≤ Real.exp v := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hv
  have htail :=
    D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hendpoint
  change Q (Real.exp v) = _ at htail
  have hquotient : Q (Real.exp v) = -U (Real.exp v) / Real.exp v := by
    rw [htail]
    dsimp [U]
    field_simp [(Real.exp_pos v).ne']
    ring
  rw [hquotient, actual_integrated_explicit_formula hv₀]
  simp only [correction, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, div_eq_mul_inv, ← Real.exp_neg]
  ring

private lemma log_spectrum_hasSum (v : ℝ) :
    HasSum (fun k : ℕ => actualCoeff k * spectralExp (actualZero k) v)
      (actualH v * (Real.exp (-v) : ℂ)) := by
  have h : HasSum (fun k : ℕ => actualCoeff k * Complex.exp ((v : ℂ) * actualZero k))
      (actualH v) := (actualH_summable v).hasSum
  have hterm (k : ℕ) : actualCoeff k * spectralExp (actualZero k) v =
      (actualCoeff k * Complex.exp ((v : ℂ) * actualZero k)) * (Real.exp (-v) : ℂ) := by
    rw [spectralExp, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simpa only [hterm] using h.mul_right (Real.exp (-v) : ℂ)

private lemma log_mode_norm_le (k : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    ‖actualCoeff k * spectralExp (actualZero k) v‖ ≤ ‖actualCoeff k‖ := by
  have hz : (actualZero k).re < 1 :=
    (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1).2.2
  have hexp : ‖spectralExp (actualZero k) v‖ ≤ 1 := by
    rw [spectralExp, Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz.le) hv
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hexp

/-- Each actual occurrence contributes its own coefficient times the compact moment. -/
theorem actual_filtered_spectral_hasSum (ν : Measure ℝ) [IsProbabilityMeasure ν] {h t : ℝ}
    (hν : ν (Icc 0 h) = 1) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => actualCoeff k * expMoment ν (actualZero k - 1) *
      spectralExp (actualZero k) t)
      (∫ s : ℝ, actualH (t + s) * (Real.exp (-(t + s)) : ℂ) ∂ν) := by
  let F : ℕ → ℝ → ℂ := fun k s => actualCoeff k * spectralExp (actualZero k) (t + s)
  let bound : ℕ → ℝ → ℝ := fun k _ => ‖actualCoeff k‖
  have hs := ae_nonneg_shift ν hν
  have hF (k : ℕ) : AEStronglyMeasurable (F k) ν := by
    have hc : Continuous (F k) := by
      dsimp only [F, spectralExp]
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ s ∂ν, ‖F k s‖ ≤ bound k s :=
    hs.mono fun _ hs₀ => log_mode_norm_le k (add_nonneg ht hs₀)
  have hbsum : ∀ᵐ s ∂ν, Summable (fun k : ℕ => bound k s) :=
    ae_of_all ν fun _ => actualCoeff_hasSum.summable.norm
  have hbint : Integrable (fun s : ℝ => ∑' k : ℕ, bound k s) ν :=
    integrable_const (∑' k : ℕ, ‖actualCoeff k‖)
  have hlim : ∀ᵐ s : ℝ ∂ν, HasSum (fun k : ℕ => F k s)
      (actualH (t + s) * (Real.exp (-(t + s)) : ℂ)) :=
    ae_of_all ν fun s => log_spectrum_hasSum (t + s)
  have hsum := hasSum_integral_of_dominated_convergence bound hF hbound hbsum hbint hlim
  have hsplit (k : ℕ) (s : ℝ) : F k s =
      (actualCoeff k * spectralExp (actualZero k) t) *
        Complex.exp ((actualZero k - 1) * (s : ℂ)) := by
    simp only [F, spectralExp, Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]
  have hterm (k : ℕ) : (∫ s, F k s ∂ν) =
      actualCoeff k * expMoment ν (actualZero k - 1) * spectralExp (actualZero k) t := by
    calc
      _ = (actualCoeff k * spectralExp (actualZero k) t) * expMoment ν (actualZero k - 1) := by
        simp_rw [hsplit k]
        exact integral_const_mul _ _
      _ = _ := mul_right_comm _ _ _
  simpa only [hterm] using hsum

private lemma correction_bounds {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    -(Real.log (2 * Real.pi) * Real.exp (-t)) ≤ correction (t + s) ∧
      correction (t + s) ≤ 0 := by
  have hv : 0 ≤ t + s := add_nonneg ht hs
  have hlog : 1 < Real.log (2 * Real.pi) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    exact Real.exp_one_lt_three.trans (by linarith [Real.pi_gt_three])
  have htriv : trivialT (t + s) ≤ 1 :=
    (trivialT_le_mass hv).trans (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)])
  have hexp : Real.exp (-(t + s)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
  unfold correction
  constructor
  · calc
      _ ≤ -(Real.log (2 * Real.pi) * Real.exp (-(t + s))) :=
        neg_le_neg (mul_le_mul_of_nonneg_left hexp (by linarith))
      _ = (-Real.log (2 * Real.pi)) * Real.exp (-(t + s)) := by rw [neg_mul]
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right (by linarith [trivialT_nonneg hv]) (Real.exp_nonneg _)
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (htriv.trans hlog.le))
      (Real.exp_nonneg _)

private lemma correction_integrable {ν : Measure ℝ} [IsProbabilityMeasure ν] {t : ℝ}
    (ht : 0 ≤ t) (hs : ∀ᵐ s ∂ν, 0 ≤ s) : Integrable (fun s => correction (t + s)) ν := by
  have htriv : Continuous (fun s : ℝ => trivialT (max (t + s) 0)) :=
    trivialT_continuousOn.comp_continuous (by fun_prop)
      (fun s => Set.mem_Ici.mpr (le_max_right (t + s) 0))
  have hT : AEStronglyMeasurable (fun s : ℝ => trivialT (t + s)) ν :=
    htriv.aestronglyMeasurable.congr <| hs.mono fun s hs₀ => by
      simp only [max_eq_left (add_nonneg ht hs₀)]
  have hexp : Continuous (fun s : ℝ => Real.exp (-(t + s))) := by fun_prop
  refine (integrable_const (Real.log (2 * Real.pi) * Real.exp (-t))).mono'
    ((hT.sub aestronglyMeasurable_const).mul hexp.aestronglyMeasurable) ?_
  filter_upwards [hs] with s hs₀
  obtain ⟨hlower, hupper⟩ := correction_bounds ht hs₀
  rw [Real.norm_eq_abs, abs_of_nonpos hupper]
  exact neg_le_of_neg_le hlower

/-- The signed correction lies between `-log (2π) * exp (-t)` and zero. -/
theorem averagedActualCorrection_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] {h t : ℝ}
    (hν : ν (Icc 0 h) = 1) (ht : 0 ≤ t) :
    -(Real.log (2 * Real.pi) * Real.exp (-t)) ≤ averagedActualCorrection ν t ∧
      averagedActualCorrection ν t ≤ 0 := by
  have hs := ae_nonneg_shift ν hν
  unfold averagedActualCorrection
  constructor
  · have hlower := integral_mono_ae (integrable_const (-(Real.log (2 * Real.pi) * Real.exp (-t))))
      (correction_integrable ht hs) (hs.mono fun _ hs₀ => (correction_bounds ht hs₀).1)
    simpa only [integral_const, probReal_univ, one_smul] using hlower
  · exact integral_nonpos_of_ae (hs.mono fun _ hs₀ => (correction_bounds ht hs₀).2)

/-- The exact compact average of the actual complete Chebyshev log-tail. -/
theorem actual_filtered_explicit_formula (ν : Measure ℝ) [IsProbabilityMeasure ν] {h t : ℝ}
    (hν : ν (Icc 0 h) = 1) (ht : Real.log 2 ≤ t) :
    (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
      -(∑' k : ℕ, actualCoeff k * expMoment ν (actualZero k - 1) *
        spectralExp (actualZero k) t).re + averagedActualCorrection ν t := by
  have ht₀ : 0 ≤ t := (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans ht
  have hs := ae_nonneg_shift ν hν
  let H : ℝ → ℂ := fun s => actualH (t + s) * (Real.exp (-(t + s)) : ℂ)
  have hH : Integrable H ν := by
    have hshift : Continuous (fun s : ℝ => t + s) := by fun_prop
    have hc : Continuous H := by
      unfold H
      exact (actualH_continuous.comp hshift).mul (by fun_prop)
    refine (integrable_const (∑' k : ℕ, ‖actualCoeff k‖)).mono' hc.aestronglyMeasurable ?_
    filter_upwards [hs] with s hs₀
    exact (log_spectrum_hasSum (t + s)).norm_le_of_bounded
      actualCoeff_hasSum.summable.norm.hasSum (fun k => log_mode_norm_le k (add_nonneg ht₀ hs₀))
  have hpoint : (fun s : ℝ => Q (Real.exp (t + s))) =ᵐ[ν]
      (fun s : ℝ => -(H s).re + correction (t + s)) :=
    hs.mono fun s hs₀ => q_exp_eq (v := t + s) (by linarith)
  have hre : (∫ s, (H s).re ∂ν) = (∫ s, H s ∂ν).re := by
    simpa only [RCLike.re_eq_complex_re] using integral_re hH
  have hadd := integral_add hH.re.neg (correction_integrable ht₀ hs)
  simp only [Pi.neg_apply, RCLike.re_eq_complex_re] at hadd
  have hsum := (actual_filtered_spectral_hasSum ν hν ht₀).tsum_eq
  change (∑' k : ℕ, actualCoeff k * expMoment ν (actualZero k - 1) *
    spectralExp (actualZero k) t) = (∫ s, H s ∂ν) at hsum
  rw [integral_congr_ae hpoint, hadd, integral_neg, hre, hsum, averagedActualCorrection]

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredExplicitFormula
