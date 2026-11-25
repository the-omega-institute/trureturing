/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: The W-weighted resolvent yields a cubic split for actual zero occurrences. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint

/-! The original Laplace weight and the full actual zero occurrence family yield
a cubic bound for the spectral contribution at a positive endpoint. -/

set_option autoImplicit false
noncomputable section

open Real Set Filter MeasureTheory
open D5.S3.Weil.Mertens.IntegratedExplicit.CountableResolvent
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualSignedGaussianEndpoint (actualCompleteSpectrum)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint

/-- Retain the endpoint exponential and the denominator at the start of the Laplace ray. -/
theorem resolventMode_norm_le {z : ℂ} (hz : z.re ≤ 1) (hz₁ : (1 : ℂ) - z ≠ 0)
    {b : ℝ} (hb : 0 < b) :
    ‖resolventMode z b‖ ≤ W b * exp ((z.re - 1) * b) / ‖(1 : ℂ) - z‖ := by
  have hzNorm : 0 < ‖(1 : ℂ) - z‖ := norm_pos_iff.mpr hz₁
  have hkernel : ∀ᵐ s : ℝ ∂volume.restrict (Ioi 0),
      ‖resolventKernel z s b‖ ≤ s * (1 + s) * exp (-s * b) *
        exp ((z.re - 1) * b) / ‖(1 : ℂ) - z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hden : ‖(1 : ℂ) - z‖ ≤ ‖denominator z s‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      simp only [Complex.sq_norm, Complex.normSq_apply, denominator, Complex.sub_re,
        Complex.add_re, Complex.ofReal_re, Complex.one_re, Complex.sub_im, Complex.add_im,
        Complex.ofReal_im, Complex.one_im, add_zero]
      nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hz), sq_nonneg s]
    have hexp : ‖Complex.exp (-denominator z s * b)‖ =
        exp (-s * b) * exp ((z.re - 1) * b) := by
      rw [Complex.norm_exp, ← exp_add]
      congr 1
      simp only [denominator, Complex.mul_re, Complex.neg_re, Complex.sub_re, Complex.add_re,
        Complex.ofReal_re, Complex.one_re, Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [resolventKernel, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (laplacePolynomial_nonneg hs.le), hexp]
    calc
      _ ≤ (laplacePolynomial s / ‖(1 : ℂ) - z‖) *
          (exp (-s * b) * exp ((z.re - 1) * b)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (laplacePolynomial_nonneg hs.le) hzNorm hden)
          (mul_nonneg (exp_nonneg _) (exp_nonneg _))
      _ = _ := by unfold laplacePolynomial; ring
  have h := norm_integral_le_of_norm_le
    (((laplace_weight_integrable hb).mul_const (exp ((z.re - 1) * b))).div_const
      ‖(1 : ℂ) - z‖) hkernel
  simpa only [resolventMode, integral_div, integral_mul_const, laplace_weight hb] using h

/-- Low occurrences include both signs and every multiplicity at the cutoff. -/
def lowHeight (T : ℝ) : Set ℕ := {k | |(actualZero k).im| ≤ T}

/-- Cubic mass on the low occurrences. -/
def cubicLowMass (T : ℝ) : ℝ := ∑' k : lowHeight T, 1 / |(actualZero k).im| ^ 3

/-- Inverse-square mass on the complement of the low occurrences. -/
def quadraticHighMass (T : ℝ) : ℝ := ∑' k : ((lowHeight T)ᶜ : Set ℕ), 1 / |(actualZero k).im| ^ 2

private theorem actual_mode_norm_le (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ‖actualCoeff k * resolventMode (actualZero k) b‖ ≤
      W b * exp (((actualZero k).re - 1) * b) / |(actualZero k).im| ^ 3 := by
  let z := actualZero k
  have hγ : 0 < |z.im| := (by norm_num : (0 : ℝ) < 10).trans (actualCompleteSpectrum.height k)
  have ha : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hb' : |z.im| ≤ ‖1 - z‖ := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
      Complex.abs_im_le_norm (1 - z)
  have h1 : (1 : ℂ) - z ≠ 0 := norm_pos_iff.mp (hγ.trans_le hb')
  have hstrip : z.re ≤ 1 := (actualCompleteSpectrum.strip k).2.le
  have hcoeff : ‖actualCoeff k‖ = 1 / (‖z‖ * ‖1 - z‖) := by
    simp only [actualCoeff, norm_div, norm_one, norm_mul, z]
  have hprod : |z.im| ^ 3 ≤ ‖z‖ * ‖1 - z‖ * ‖1 - z‖ := by
    rw [pow_succ, sq]
    exact mul_le_mul (mul_le_mul ha hb' hγ.le (norm_nonneg _)) hb'
      hγ.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_mul]
  calc
    _ ≤ ‖actualCoeff k‖ * (W b * exp ((z.re - 1) * b) / ‖1 - z‖) :=
      mul_le_mul_of_nonneg_left (resolventMode_norm_le hstrip h1 hb) (norm_nonneg _)
    _ = W b * exp ((z.re - 1) * b) / (‖z‖ * ‖1 - z‖ * ‖1 - z‖) := by
      rw [hcoeff]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (W_nonneg hb.le) (exp_nonneg _)) (pow_pos hγ _) hprod

/-- A finite-height critical-line premise gives a low cubic mass and a high
inverse-square tail. The high mass is also bounded by the full Li mass estimate. -/
theorem actual_spectral_tail_bound {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hcritical : ∀ k ∈ lowHeight T, (actualZero k).re = 1 / 2) :
    (lowHeight T).Finite ∧
    ‖spectralTail actualCompleteSpectrum b‖ ≤
      W b * (exp (-b / 2) * cubicLowMass T + quadraticHighMass T / T) ∧
    quadraticHighMass T ≤ (101 / 100 : ℝ) * firstLiMass := by
  let q (k : ℕ) := 1 / |(actualZero k).im| ^ 2
  let c (k : ℕ) := 1 / |(actualZero k).im| ^ 3
  let f (k : ℕ) := actualCoeff k * resolventMode (actualZero k) b
  have hq : Summable q := by
    simpa only [q, sq_abs, one_div, inv_pow, Function.comp_def, actualZero] using
      (actualOccurrenceEquiv.summable_iff).2 actual_sigma_inverse_square_summable
  have hq0 (k : ℕ) : 0 ≤ q k := by dsimp [q]; positivity
  have hc0 (k : ℕ) : 0 ≤ c k := by dsimp [c]; positivity
  have hγ (k : ℕ) : 0 < |(actualZero k).im| :=
    (by norm_num : (0 : ℝ) < 10).trans (actualCompleteSpectrum.height k)
  have hcompare (k : ℕ) {L : ℝ} (hL : 0 < L) (hk : L ≤ |(actualZero k).im|) :
      c k ≤ q k / L := by
    dsimp [c, q]
    rw [div_div, pow_succ]
    exact one_div_le_one_div_of_le (mul_pos (pow_pos (hγ k) _) hL)
      (mul_le_mul_of_nonneg_left hk (sq_nonneg _))
  have hf : Summable (fun k => ‖f k‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hq.mul_left (W b))
    intro k
    have he : exp (((actualZero k).re - 1) * b) ≤ 1 :=
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (actualCompleteSpectrum.strip k).2.le) hb.le)
    calc
      ‖f k‖ ≤ W b * exp (((actualZero k).re - 1) * b) * c k := by
        simpa only [f, c, div_eq_mul_inv, one_mul] using actual_mode_norm_le k hb
      _ ≤ W b * 1 * (q k / 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (W_nonneg hb.le))
          (hcompare k one_pos ((by norm_num : (1 : ℝ) ≤ 10).trans
            (actualCompleteSpectrum.height k).le))
          (hc0 k) (mul_nonneg (W_nonneg hb.le) zero_le_one)
      _ = W b * q k := by simp
  have hfinite : (lowHeight T).Finite := by
    have hp : 0 < 1 / T ^ 2 := by positivity
    have hev : ∀ᶠ k in cofinite, q k < 1 / T ^ 2 :=
      hq.tendsto_cofinite_zero.eventually (gt_mem_nhds hp)
    refine (eventually_cofinite.mp hev).subset ?_
    intro k hk
    exact not_lt_of_ge (one_div_le_one_div_of_le (pow_pos (hγ k) _)
      (pow_le_pow_left₀ (abs_nonneg _) (show |(actualZero k).im| ≤ T from hk) 2))
  have hlow : Summable (fun k : lowHeight T => c k) := by
    let := hfinite.fintype
    exact Summable.of_finite
  have hhigh : Summable (fun k : ((lowHeight T)ᶜ : Set ℕ) => q k) := hq.subtype _
  have hl : (∑' k : lowHeight T, ‖f k‖) ≤ W b * (exp (-b / 2) * cubicLowMass T) := by
    rw [cubicLowMass, ← tsum_mul_left, ← tsum_mul_left]
    refine (hf.subtype _).tsum_le_tsum (fun k => ?_) ((hlow.mul_left _).mul_left _)
    have he : exp (((actualZero k).re - 1) * b) = exp (-b / 2) := by
      rw [hcritical k k.property]
      congr 1
      ring
    simpa only [f, c, div_eq_mul_inv, one_mul, he, mul_assoc] using actual_mode_norm_le k hb
  have hh : (∑' k : ((lowHeight T)ᶜ : Set ℕ), ‖f k‖) ≤ W b * (quadraticHighMass T / T) := by
    rw [quadraticHighMass, ← tsum_div_const, ← tsum_mul_left]
    refine (hf.subtype _).tsum_le_tsum (fun k => ?_) ((hhigh.div_const _).mul_left _)
    have he : exp (((actualZero k).re - 1) * b) ≤ 1 :=
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (actualCompleteSpectrum.strip k).2.le) hb.le)
    have hk : T ≤ |(actualZero k).im| :=
      (lt_of_not_ge (show ¬ |(actualZero k).im| ≤ T from k.property)).le
    calc
      ‖f k‖ ≤ W b * exp (((actualZero k).re - 1) * b) * c k := by
        simpa only [f, c, div_eq_mul_inv, one_mul] using actual_mode_norm_le k hb
      _ ≤ W b * 1 * (q k / T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (W_nonneg hb.le))
          (hcompare k hT hk) (hc0 k) (mul_nonneg (W_nonneg hb.le) zero_le_one)
      _ = W b * (q k / T) := by rw [mul_one]
  refine ⟨hfinite, ?_, ?_⟩
  · rw [countable_resolvent_identity actualCompleteSpectrum hb]
    change ‖∑' k, f k‖ ≤ _
    have hsplit := (hf.subtype (lowHeight T)).tsum_add_tsum_compl
      (hf.subtype (lowHeight T)ᶜ)
    rw [mul_add]
    exact (norm_tsum_le_tsum_norm hf).trans (hsplit.symm.le.trans (add_le_add hl hh))
  · have hle := Summable.tsum_subtype_le q (lowHeight T)ᶜ hq0 hq
    exact hle.trans (by simpa only [q, sq_abs, one_div, inv_pow] using
      actual_inverse_square_mass_le_height)

#print axioms resolventMode_norm_le
#print axioms actual_spectral_tail_bound

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualCubicEndpoint
