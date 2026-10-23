/- GID: D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiFiniteGammaEnergy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-domain-refutation)
   anchors: []
   utility: none
   digest: Unbounded finite Gamma energy under a strict physical moment cap. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy

open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample

open MeasureTheory Set Filter
open scoped ENNReal FourierTransform Topology Function

private theorem finiteTent_le_one (s : ℝ) : tent s ≤ 1 := by
  unfold tent
  apply max_le
  · linarith [abs_nonneg s]
  · norm_num

private def finiteProfile (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N + 1), spatialTerm n t

private def finiteAmplitude (N : ℕ) (ξ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), spectralTerm n ξ

private def finiteCompressedProfile (N : ℕ) (κ t : ℝ) : ℂ :=
  finiteProfile N (t / κ)

private def finitePhysicalFeature (N : ℕ) (κ : ℝ) : ℝ → ℂ :=
  sourceOfProfile (finiteCompressedProfile N κ)

private theorem finiteProfile_continuous (N : ℕ) : Continuous (finiteProfile N) := by
  unfold finiteProfile
  apply continuous_finsetSum
  intro n hn
  unfold spatialTerm tent
  fun_prop

private theorem finiteProfile_zero_off (N : ℕ) {t : ℝ}
    (ht : t ∉ Icc (1 / 4 : ℝ) (3 / 4)) : finiteProfile N t = 0 := by
  have habs : (1 / 4 : ℝ) ≤ |t - 1 / 2| := by
    by_contra h
    have hs := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨by linarith [hs.1], by linarith [hs.2]⟩
  unfold finiteProfile
  apply Finset.sum_eq_zero
  intro n hn
  simp only [spatialTerm, tent_zero_of_quarter_le habs, mul_zero, zero_mul,
    Complex.ofReal_zero]


private theorem finiteProfile_real (N : ℕ) (t : ℝ) : (finiteProfile N t).im = 0 := by
  simp only [finiteProfile, Complex.im_sum, spatialTerm, Complex.ofReal_im,
    Finset.sum_const_zero]

private theorem finiteProfile_norm_le (N : ℕ) (t : ℝ) : ‖finiteProfile N t‖ ≤ 1 := by
  have hc : (∑ n ∈ Finset.range (N + 1), coeff n) ≤ 1 := by
    simpa only [coeff_hasSum.tsum_eq] using
      Summable.sum_le_tsum (Finset.range (N + 1))
        (fun n hn => coeff_nonneg n) coeff_hasSum.summable
  calc
    ‖finiteProfile N t‖ ≤ ∑ n ∈ Finset.range (N + 1), ‖spatialTerm n t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), coeff n := by
      apply Finset.sum_le_sum
      intro n hn
      have hk := actual_kernel_term_norm_bound 0 t n
      have hb := mul_le_of_le_one_right (coeff_nonneg n) (finiteTent_le_one (t - 1 / 2))
      rw [norm_mul, sourcePhase_norm, one_mul] at hk
      exact hk.trans hb
    _ ≤ 1 := hc

private theorem finiteProfile_fourier (N : ℕ) (ξ : ℝ) :
    unitarySourceFourier (finiteProfile N) ξ =
      sourcePhase ξ (1 / 2) * (finiteAmplitude N ξ : ℂ) := by
  have hsingle (n : ℕ) :
      Integrable (fun t : ℝ => sourcePhase ξ t * spatialTerm n t) := by
    have hs : HasCompactSupport (fun t : ℝ => sourcePhase ξ t * spatialTerm n t) := by
      apply HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 3 / 4))
      intro t ht
      by_contra h
      have habs : (1 / 4 : ℝ) ≤ |t - 1 / 2| := by
        by_contra hh
        have ha := abs_lt.mp (lt_of_not_ge hh)
        exact h ⟨by linarith [ha.1], by linarith [ha.2]⟩
      exact ht (by simp only [spatialTerm, tent_zero_of_quarter_le habs,
        mul_zero, zero_mul, Complex.ofReal_zero])
    apply Continuous.integrable_of_hasCompactSupport _ hs
    unfold sourcePhase spatialTerm tent
    fun_prop
  rw [unitarySourceFourier_eq_integral]
  unfold finiteProfile
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun n hn => hsingle n), Finset.mul_sum]
  calc
    _ = ∑ n ∈ Finset.range (N + 1), unitarySourceFourier (spatialTerm n) ξ := by
      simp only [unitarySourceFourier_eq_integral]
    _ = sourcePhase ξ (1 / 2) * (finiteAmplitude N ξ : ℂ) := by
      simp only [actual_spatial_term_fourier, finiteAmplitude,
        Complex.ofReal_sum, Finset.mul_sum]

private theorem finiteAmplitude_nonneg (N : ℕ) (ξ : ℝ) : 0 ≤ finiteAmplitude N ξ :=
  Finset.sum_nonneg (fun n hn => spectralTerm_nonneg n ξ)

private theorem finiteAmplitude_continuous (N : ℕ) : Continuous (finiteAmplitude N) := by
  unfold finiteAmplitude spectralTerm
  apply continuous_finsetSum
  intro n hn
  unfold tentSourceHat
  fun_prop

private theorem finiteProfile_fourier_norm (N : ℕ) (ξ : ℝ) :
    ‖unitarySourceFourier (finiteProfile N) ξ‖ = finiteAmplitude N ξ := by
  rw [finiteProfile_fourier, norm_mul, sourcePhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (finiteAmplitude_nonneg N ξ)]

private theorem finiteCompressed_fourier (N : ℕ) {κ : ℝ} (hκ : 0 < κ) (ξ : ℝ) :
    unitarySourceFourier (finiteCompressedProfile N κ) ξ =
      (κ : ℂ) * unitarySourceFourier (finiteProfile N) (κ * ξ) := by
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hp (t : ℝ) : sourcePhase ξ t = sourcePhase (κ * ξ) (t / κ) := by
    unfold sourcePhase
    congr 1
    push_cast
    field_simp [hκc] <;> ring
  have hi : (∫ t : ℝ, sourcePhase ξ t * finiteCompressedProfile N κ t) =
      κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * finiteProfile N t := by
    calc
      _ = ∫ t : ℝ, sourcePhase (κ * ξ) (t / κ) * finiteProfile N (t / κ) := by
        apply integral_congr_ae
        filter_upwards with t
        simp only [finiteCompressedProfile, hp]
      _ = κ • ∫ t : ℝ, sourcePhase (κ * ξ) t * finiteProfile N t := by
        simpa only [abs_of_pos hκ] using
          Measure.integral_comp_div
            (fun t : ℝ => sourcePhase (κ * ξ) t * finiteProfile N t) κ
  rw [unitarySourceFourier_eq_integral, unitarySourceFourier_eq_integral, hi,
    Complex.real_smul]
  ring

private theorem finiteCompressed_fourier_norm (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (ξ : ℝ) :
    ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ =
      κ * finiteAmplitude N (κ * ξ) := by
  rw [finiteCompressed_fourier N hκ, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hκ, finiteProfile_fourier_norm]

private def finiteTentDecayConstant : ℝ := 65 / (4 * Real.sqrt (2 * Real.pi))


private theorem finiteTent_decay (η : ℝ) :
    (1 + η ^ 2) * tentSourceHat η ≤ finiteTentDecayConstant := by
  have hsinc : Real.sinc (η / 8) ^ 2 ≤ 1 := by
    have h := Real.abs_sinc_le_one (η / 8)
    calc
      Real.sinc (η / 8) ^ 2 = |Real.sinc (η / 8)| ^ 2 := (sq_abs _).symm
      _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = 1 := by norm_num
  have hη : η ^ 2 * Real.sinc (η / 8) ^ 2 ≤ 64 := by
    by_cases hz : η = 0
    · simp only [hz, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      norm_num
    · have h8 : η / 8 ≠ 0 := div_ne_zero hz (by norm_num)
      have hid : η ^ 2 * Real.sinc (η / 8) ^ 2 =
          64 * Real.sin (η / 8) ^ 2 := by
        rw [Real.sinc_of_ne_zero h8]
        field_simp [hz] <;> ring
      rw [hid]
      have hsin := abs_le.mp (Real.abs_sin_le_one (η / 8))
      nlinarith [hsin.1, hsin.2]
  have hsum : (1 + η ^ 2) * Real.sinc (η / 8) ^ 2 ≤ 65 := by
    nlinarith [hsinc, hη]
  calc
    (1 + η ^ 2) * tentSourceHat η =
        (1 / (4 * Real.sqrt (2 * Real.pi))) *
          ((1 + η ^ 2) * Real.sinc (η / 8) ^ 2) := by
      unfold tentSourceHat
      ring
    _ ≤ (1 / (4 * Real.sqrt (2 * Real.pi))) * 65 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = finiteTentDecayConstant := by unfold finiteTentDecayConstant; ring

private theorem finiteShiftedTent_decay (δ ξ : ℝ) :
    (1 + ξ ^ 2) * tentSourceHat (ξ - δ) ≤
      2 * (1 + δ ^ 2) * finiteTentDecayConstant := by
  have hrel : 1 + ξ ^ 2 ≤ 2 * (1 + δ ^ 2) * (1 + (ξ - δ) ^ 2) := by
    have hsq : ξ ^ 2 ≤ 2 * (ξ - δ) ^ 2 + 2 * δ ^ 2 := by
      nlinarith [sq_nonneg (ξ - 2 * δ)]
    nlinarith [mul_nonneg (sq_nonneg δ) (sq_nonneg (ξ - δ)), hsq]
  calc
    (1 + ξ ^ 2) * tentSourceHat (ξ - δ) ≤
        (2 * (1 + δ ^ 2) * (1 + (ξ - δ) ^ 2)) * tentSourceHat (ξ - δ) :=
      mul_le_mul_of_nonneg_right hrel (tentSourceHat_nonneg _)
    _ = (2 * (1 + δ ^ 2)) *
        ((1 + (ξ - δ) ^ 2) * tentSourceHat (ξ - δ)) := by ring
    _ ≤ 2 * (1 + δ ^ 2) * finiteTentDecayConstant :=
      mul_le_mul_of_nonneg_left (finiteTent_decay _) (by positivity)

private def finiteDecayConstant (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    2 * finiteTentDecayConstant * coeff n * (1 + frequency n ^ 2)


private theorem finiteAmplitude_decay (N : ℕ) (ξ : ℝ) :
    (1 + ξ ^ 2) * finiteAmplitude N ξ ≤ finiteDecayConstant N := by
  unfold finiteAmplitude finiteDecayConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hminus := finiteShiftedTent_decay (frequency n) ξ
  have hplus : (1 + ξ ^ 2) * tentSourceHat (ξ + frequency n) ≤
      2 * (1 + frequency n ^ 2) * finiteTentDecayConstant := by
    simpa only [sub_neg_eq_add, neg_sq] using finiteShiftedTent_decay (-frequency n) ξ
  have hcoeff : 0 ≤ coeff n / 2 := div_nonneg (coeff_nonneg n) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left (add_le_add hminus hplus) hcoeff
  unfold spectralTerm
  nlinarith [hm]

private def finiteCompressedDecayConstant (N : ℕ) (κ : ℝ) : ℝ :=
  κ * (1 + κ⁻¹ ^ 2) * finiteDecayConstant N

private theorem finiteCompressed_decay (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (ξ : ℝ) :
    (1 + ξ ^ 2) * ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ≤
      finiteCompressedDecayConstant N κ := by
  have hid : κ⁻¹ ^ 2 * (κ * ξ) ^ 2 = ξ ^ 2 := by
    field_simp [hκ.ne'] <;> ring
  have hrel : 1 + ξ ^ 2 ≤ (1 + κ⁻¹ ^ 2) * (1 + (κ * ξ) ^ 2) := by
    nlinarith [sq_nonneg κ⁻¹, sq_nonneg (κ * ξ), hid]
  rw [finiteCompressed_fourier_norm N hκ]
  calc
    (1 + ξ ^ 2) * (κ * finiteAmplitude N (κ * ξ)) ≤
        ((1 + κ⁻¹ ^ 2) * (1 + (κ * ξ) ^ 2)) *
          (κ * finiteAmplitude N (κ * ξ)) :=
      mul_le_mul_of_nonneg_right hrel
        (mul_nonneg hκ.le (finiteAmplitude_nonneg _ _))
    _ = κ * (1 + κ⁻¹ ^ 2) *
        ((1 + (κ * ξ) ^ 2) * finiteAmplitude N (κ * ξ)) := by ring
    _ ≤ finiteCompressedDecayConstant N κ :=
      mul_le_mul_of_nonneg_left (finiteAmplitude_decay N (κ * ξ)) (by positivity)

-- This is the actual weighted Fourier density. Its genuine Integrable proof
-- precedes every use of its real integral as an energy.
private theorem finiteCompressed_gamma_integrable (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun ξ : ℝ => Symbol.gammaWeight ξ *
      ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2) volume := by
  obtain ⟨G, hG, hp⟩ := Symbol.finiteGammaWeight_quadratic_upper
  let E : ℝ := finiteCompressedDecayConstant N κ
  have hcont : Continuous (fun ξ : ℝ =>
      ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖) := by
    simp_rw [finiteCompressed_fourier_norm N hκ]
    exact continuous_const.mul ((finiteAmplitude_continuous N).comp
      (continuous_const.mul continuous_id))
  refine (integrable_inv_one_add_sq.const_mul (G * E ^ 2)).mono' ?_
    (Eventually.of_forall fun ξ => ?_)
  · exact (Symbol.finiteGammaWeight_continuous.mul (hcont.pow 2)).aestronglyMeasurable
  · have hp0 : 0 ≤ Symbol.gammaWeight ξ := by
      linarith [(Symbol.actualGammaWeight_bounds ξ).1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (sq_nonneg _))]
    have hw : 0 < 1 + ξ ^ 2 := by positivity
    have hd := finiteCompressed_decay N hκ ξ
    have hs := pow_le_pow_left₀
      (mul_nonneg hw.le (norm_nonneg _)) hd 2
    have hpn := mul_le_mul_of_nonneg_right (hp ξ)
      (sq_nonneg ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖)
    apply (le_div_iff₀ hw).mpr
    change Symbol.gammaWeight ξ *
        ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2 *
        (1 + ξ ^ 2) ≤ G * E ^ 2
    have hm := mul_le_mul_of_nonneg_right hpn hw.le
    have hg := mul_le_mul_of_nonneg_left hs hG.le
    nlinarith [hm, hg]

private theorem finiteCompressed_all_shift_integrable (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (c : ℝ) :
    Integrable (fun ξ : ℝ => (Symbol.gammaWeight ξ + c) *
      ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2) volume := by
  have hGamma := finiteCompressed_gamma_integrable N hκ
  have hq : Integrable (fun ξ : ℝ =>
      ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2) volume := by
    refine hGamma.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · simp_rw [finiteCompressed_fourier_norm N hκ]
      apply Continuous.aestronglyMeasurable
      exact (continuous_const.mul ((finiteAmplitude_continuous N).comp
        (continuous_const.mul continuous_id))).pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact le_mul_of_one_le_left (sq_nonneg _) (Symbol.actualGammaWeight_bounds ξ).1.le
  convert hGamma.add (hq.const_mul c) using 1
  funext ξ
  simp only [Pi.add_apply]
  ring

private theorem finiteCompressed_zero_off (N : ℕ) {κ : ℝ} (hκ : 0 < κ)
    {t : ℝ} (ht : t ∉ Icc (κ / 4) (3 * κ / 4)) :
    finiteCompressedProfile N κ t = 0 := by
  apply finiteProfile_zero_off
  intro h
  have ha := (le_div_iff₀ hκ).mp h.1
  have hb := (div_le_iff₀ hκ).mp h.2
  exact ht ⟨by linarith [ha], by linarith [hb]⟩

private theorem finitePhysical_zero_high (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {x : ℝ} (hx : 4 * Real.pi ≤ x) :
    finitePhysicalFeature N κ x = 0 := by
  have hπ : Real.pi ≤ x := by nlinarith [Real.pi_pos]
  have hratio : (4 : ℝ) ≤ x / Real.pi := (le_div_iff₀ Real.pi_pos).mpr hx
  have hlog : 3 * κ / 4 < Real.log (x / Real.pi) := by
    have hl := (Real.log_le_log (by norm_num : (0 : ℝ) < 4) hratio)
    linarith [three_quarters_lt_log_four, hl]
  have hz : finiteCompressedProfile N κ (Real.log (x / Real.pi)) = 0 :=
    finiteCompressed_zero_off N hκ (fun h => (not_le_of_gt hlog) h.2)
  simp only [finitePhysicalFeature, sourceOfProfile, if_pos hπ, hz, mul_zero]

private theorem finitePhysical_fullHasSum (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) {x : ℝ} (hx : Real.pi ≤ x) :
    HasSum (fun k : ℕ => physicalTerm (finitePhysicalFeature N κ) k x)
      (finitePhysicalFeature N κ x) := by
  have ht (k : ℕ) (hk : k ≠ 0) :
      physicalTerm (finitePhysicalFeature N κ) k x = 0 := by
    have hn : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ k + 1)
    have hn2 : (4 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by nlinarith
    have hy : 4 * Real.pi ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) * x := by
      nlinarith [mul_le_mul_of_nonneg_right hn2 (le_trans Real.pi_pos.le hx)]
    simp only [physicalTerm, finitePhysical_zero_high N hκ hκ1 hy, mul_zero]
  have hf : (fun k : ℕ => physicalTerm (finitePhysicalFeature N κ) k x) =
      fun k : ℕ => if k = 0 then finitePhysicalFeature N κ x else 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp [physicalTerm]
    · simp only [if_neg hk, ht k hk]
  rw [hf]
  exact hasSum_ite_eq 0 (finitePhysicalFeature N κ x)

private theorem finitePhysical_actualProfile_eq (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    actualGammaProfile (finitePhysicalFeature N κ) = finiteCompressedProfile N κ := by
  funext t
  by_cases ht : 0 ≤ t
  · have hxpos : 0 < Real.pi * Real.exp t := mul_pos Real.pi_pos (Real.exp_pos t)
    have hx : Real.pi ≤ Real.pi * Real.exp t := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (Real.one_le_exp_iff.mpr ht) Real.pi_pos.le
    have hf : fullTheta (finitePhysicalFeature N κ) (Real.pi * Real.exp t) =
        finitePhysicalFeature N κ (Real.pi * Real.exp t) :=
      (finitePhysical_fullHasSum N hκ hκ1 hx).tsum_eq
    have hl : Real.log ((Real.pi * Real.exp t) / Real.pi) = t := by
      rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
    have hr : (Real.pi * Real.exp t) ^ (9 / 4 : ℝ) *
        (Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) = 1 := by
      rw [← Real.rpow_add hxpos]
      norm_num
    have hrc : (((Real.pi * Real.exp t) ^ (9 / 4 : ℝ) : ℝ) : ℂ) *
        (((Real.pi * Real.exp t) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hr
    rw [actualGammaProfile, if_pos ht, hf, finitePhysicalFeature, sourceOfProfile,
      if_pos hx, hl, ← mul_assoc, hrc, one_mul]
  · have hz : finiteCompressedProfile N κ t = 0 :=
      finiteCompressed_zero_off N hκ (fun h => by linarith [h.1])
    simp only [actualGammaProfile, if_neg ht, hz]

-- Actual physical feature, entire theta, and genuinely finite form energy.
-- This consumer proves every real constant-shift integrand integrable.
private theorem finitePhysical_in_all_shift_domains (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (c : ℝ) :
    originalGammaFormDomain c (finitePhysicalFeature N κ) := by
  unfold originalGammaFormDomain
  rw [finitePhysical_actualProfile_eq N hκ hκ1]
  exact finiteCompressed_all_shift_integrable N hκ c

private theorem finiteAmplitude_band_lower (N n : ℕ)
    (hn : n ∈ Finset.range (N + 1)) {ξ : ℝ} (hξ : ξ ∈ positiveBand n) :
    coeff n / (32 * Real.sqrt (2 * Real.pi)) ≤ finiteAmplitude N ξ := by
  have hdist : |ξ - frequency n| ≤ 1 := by
    apply abs_le.mpr
    change ξ ∈ Icc (frequency n - 1) (frequency n + 1) at hξ
    constructor <;> linarith [hξ.1, hξ.2]
  have hpulse := tentSourceHat_lower_unit hdist
  have hother := tentSourceHat_nonneg (ξ + frequency n)
  have hcoeff : 0 ≤ coeff n / 2 := div_nonneg (coeff_nonneg n) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hpulse hcoeff
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have ht : coeff n / (32 * Real.sqrt (2 * Real.pi)) ≤ spectralTerm n ξ := by
    unfold spectralTerm
    have hbase : coeff n / (32 * Real.sqrt (2 * Real.pi)) =
        (coeff n / 2) * (1 / (16 * Real.sqrt (2 * Real.pi))) := by
      field_simp [hs.ne'] <;> ring
    rw [hbase]
    nlinarith [hm, mul_nonneg hcoeff hother]
  exact ht.trans (Finset.single_le_sum (fun m hm => spectralTerm_nonneg m ξ) hn)

private theorem finiteAmplitude_band_density_lower (N n : ℕ)
    (hn : n ∈ Finset.range (N + 1)) {ξ : ℝ} (hξ : ξ ∈ positiveBand n) :
    1 / (4096 * Real.pi) ≤
      max (Real.log |ξ|) 0 * finiteAmplitude N ξ ^ 2 := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := by unfold s; positivity
  have hs2 : s ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hA := finiteAmplitude_band_lower N n hn hξ
  have hbase0 : 0 ≤ coeff n / (32 * s) :=
    div_nonneg (coeff_nonneg n) (by positivity)
  have hA2 := pow_le_pow_left₀ hbase0 hA 2
  have hL := positiveBand_log_lower n hξ
  have hprod := mul_le_mul hL hA2 (sq_nonneg _) (le_max_right (Real.log |ξ|) 0)
  calc
    1 / (4096 * Real.pi) =
        (Real.log (frequency n) / 2) * (coeff n / (32 * s)) ^ 2 := by
      symm
      calc
        (Real.log (frequency n) / 2) * (coeff n / (32 * s)) ^ 2 =
            (coeff n ^ 2 * Real.log (frequency n)) / (2048 * s ^ 2) := by
          field_simp [hs.ne'] <;> ring
        _ = 1 / (4096 * Real.pi) := by
          rw [coeff_sq_log_frequency, hs2]
          congr 1
          ring
    _ ≤ max (Real.log |ξ|) 0 * finiteAmplitude N ξ ^ 2 := hprod

private theorem finiteCompressed_band_density_lower (N n : ℕ)
    (hn : n ∈ Finset.range (N + 1)) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {ξ : ℝ} (hξ : κ * ξ ∈ positiveBand n) :
    κ ^ 2 / (4096 * Real.pi) ≤ max (Real.log |ξ|) 0 *
      ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2 := by
  have hbase := mul_le_mul_of_nonneg_left
    (finiteAmplitude_band_density_lower N n hn hξ) (sq_nonneg κ)
  have hlog := compressed_logplus_comparison hκ hκ1 ξ
  have hm := mul_le_mul_of_nonneg_right hlog
    (mul_nonneg (sq_nonneg κ) (sq_nonneg (finiteAmplitude N (κ * ξ))))
  rw [finiteCompressed_fourier_norm N hκ, mul_pow]
  calc
    κ ^ 2 / (4096 * Real.pi) = κ ^ 2 * (1 / (4096 * Real.pi)) := by ring
    _ ≤ κ ^ 2 * (max (Real.log |κ * ξ|) 0 * finiteAmplitude N (κ * ξ) ^ 2) := hbase
    _ = max (Real.log |κ * ξ|) 0 * (κ ^ 2 * finiteAmplitude N (κ * ξ) ^ 2) := by ring
    _ ≤ max (Real.log |ξ|) 0 * (κ ^ 2 * finiteAmplitude N (κ * ξ) ^ 2) := hm

private theorem finiteProfile_uniform_tail (N : ℕ) (t : ℝ) :
    ‖counterProfile t - finiteProfile N t‖ ≤ (1 / 2 : ℝ) ^ (N + 1) := by
  let r : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hcoeff (n : ℕ) : coeff (n + (N + 1)) = r * coeff n := by
    unfold coeff r
    rw [← pow_add]
    congr 1
    omega
  have hc : HasSum (fun n : ℕ => coeff (n + (N + 1))) r := by
    simpa only [hcoeff, mul_one] using coeff_hasSum.mul_left r
  have hs : HasSum (fun n : ℕ => spatialTerm (n + (N + 1)) t)
      (counterProfile t - finiteProfile N t) := by
    simpa only [finiteProfile] using
      (hasSum_nat_add_iff' (N + 1)).mpr (actual_spatial_series_hasSum t)
  have hbound (n : ℕ) : ‖spatialTerm (n + (N + 1)) t‖ ≤
      coeff (n + (N + 1)) := by
    have hk := actual_kernel_term_norm_bound 0 t (n + (N + 1))
    rw [norm_mul, sourcePhase_norm, one_mul] at hk
    exact hk.trans (mul_le_of_le_one_right (coeff_nonneg _) (finiteTent_le_one _))
  have ht := tsum_of_norm_bounded hc hbound
  rw [hs.tsum_eq] at ht
  exact ht

private theorem finitePhysical_uniform_tail (N : ℕ) {κ : ℝ} (hκ : 0 < κ)
    (x : ℝ) :
    ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ≤
      (1 / 2 : ℝ) ^ (N + 1) := by
  have hr : 0 ≤ (1 / 2 : ℝ) ^ (N + 1) := by positivity
  by_cases hx : Real.pi ≤ x
  · have hx1 : 1 ≤ x := by linarith [Real.one_le_pi_div_two]
    have hp0 : 0 ≤ x ^ (-9 / 4 : ℝ) := Real.rpow_nonneg (by linarith [Real.pi_pos]) _
    have hp1 : x ^ (-9 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    simp only [compressedFeature, finitePhysicalFeature, sourceOfProfile, if_pos hx,
      compressedProfile, finiteCompressedProfile, ← mul_sub, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0]
    exact (mul_le_mul_of_nonneg_left
      (finiteProfile_uniform_tail N (Real.log (x / Real.pi) / κ)) hp0).trans
        (mul_le_of_le_one_left hr hp1)
  · simp only [compressedFeature, finitePhysicalFeature, sourceOfProfile, if_neg hx,
      sub_self, norm_zero]
    exact hr

private theorem finiteCompressed_continuous (N : ℕ) (κ : ℝ) :
    Continuous (finiteCompressedProfile N κ) :=
  (finiteProfile_continuous N).comp (continuous_id.div_const κ)

private theorem finiteCompressed_zero (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    finiteCompressedProfile N κ 0 = 0 :=
  finiteCompressed_zero_off N hκ (fun h => by linarith [h.1])

private theorem finiteProfile_center_ne (N : ℕ) : finiteProfile N (1 / 2) ≠ 0 := by
  have hp : 0 < ∑ n ∈ Finset.range (N + 1), coeff n :=
    Finset.sum_pos' (fun n hn => coeff_nonneg n)
      ⟨0, by simp, coeff_positive 0⟩
  have he : finiteProfile N (1 / 2) =
      ((∑ n ∈ Finset.range (N + 1), coeff n : ℝ) : ℂ) := by
    simp [finiteProfile, spatialTerm, tent, Complex.ofReal_sum]
  rw [he]
  exact_mod_cast hp.ne'

private theorem finiteCompressed_center_ne (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    finiteCompressedProfile N κ (κ / 2) ≠ 0 := by
  have hd : (κ / 2) / κ = (1 / 2 : ℝ) := by field_simp [hκ.ne']
  simpa only [finiteCompressedProfile, hd] using finiteProfile_center_ne N

private theorem finitePhysical_center_ne (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    finitePhysicalFeature N κ (Real.pi * Real.exp (κ / 2)) ≠ 0 := by
  have hx : Real.pi ≤ Real.pi * Real.exp (κ / 2) := by
    have he := Real.one_le_exp_iff.mpr (by positivity : 0 ≤ κ / 2)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hl : Real.log ((Real.pi * Real.exp (κ / 2)) / Real.pi) = κ / 2 := by
    rw [mul_div_cancel_left₀ _ Real.pi_ne_zero, Real.log_exp]
  have hn : (Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (mul_pos Real.pi_pos (Real.exp_pos _)) _).ne'
  have hnc : (((Real.pi * Real.exp (κ / 2)) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast hn
  simp only [finitePhysicalFeature, sourceOfProfile, if_pos hx, hl]
  exact mul_ne_zero hnc (finiteCompressed_center_ne N hκ)

private theorem finitePhysical_real (N : ℕ) (κ x : ℝ) :
    (finitePhysicalFeature N κ x).im = 0 := by
  by_cases hx : Real.pi ≤ x <;>
    simp [finitePhysicalFeature, sourceOfProfile, hx, finiteCompressedProfile,
      Complex.mul_im, finiteProfile_real]

private theorem finitePhysical_support (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Function.support (finitePhysicalFeature N κ) ⊆
      Icc Real.pi (Real.pi * Real.exp (3 * κ / 4)) := by
  intro x hx
  have hπ : Real.pi ≤ x := by
    by_contra h
    exact hx (by simp [finitePhysicalFeature, sourceOfProfile, h])
  refine ⟨hπ, ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le Real.pi_pos hπ
  have hprof : finiteCompressedProfile N κ (Real.log (x / Real.pi)) ≠ 0 := by
    intro hz
    exact hx (by simp [finitePhysicalFeature, sourceOfProfile, hπ, hz])
  have ht : Real.log (x / Real.pi) ∈ Icc (κ / 4) (3 * κ / 4) := by
    by_contra h
    exact hprof (finiteCompressed_zero_off N hκ h)
  have he := Real.exp_le_exp.mpr ht.2
  rw [Real.exp_log (div_pos hxpos Real.pi_pos)] at he
  simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp he

private theorem finitePhysical_compact (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (finitePhysicalFeature N κ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (finitePhysical_support N hκ)

-- Clamp x at pi only for the continuity proof; the literal source definition
-- and all physical/full-theta identities remain unchanged.
private theorem finitePhysical_continuous (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Continuous (finitePhysicalFeature N κ) := by
  have he : finitePhysicalFeature N κ = fun x : ℝ =>
      (((max Real.pi x) ^ (-9 / 4 : ℝ) : ℝ) : ℂ) *
        finiteCompressedProfile N κ (Real.log (max Real.pi x / Real.pi)) := by
    funext x
    by_cases hx : Real.pi ≤ x
    · simp [finitePhysicalFeature, sourceOfProfile, hx, max_eq_right hx]
    · simp [finitePhysicalFeature, sourceOfProfile, hx,
        max_eq_left (le_of_not_ge hx), Real.pi_ne_zero, finiteCompressed_zero N hκ]
  rw [he]
  have hm : Continuous (fun x : ℝ => max Real.pi x) := continuous_const.max continuous_id
  have hn (x : ℝ) : max Real.pi x ≠ 0 :=
    (lt_of_lt_of_le Real.pi_pos (le_max_left _ _)).ne'
  have hr := hm.rpow_const (p := (-9 / 4 : ℝ)) (fun x => Or.inl (hn x))
  have hl : Continuous (fun x : ℝ => Real.log (max Real.pi x / Real.pi)) :=
    (hm.div_const Real.pi).log (fun x => div_ne_zero (hn x) Real.pi_ne_zero)
  exact (Complex.continuous_ofReal.comp hr).mul ((finiteCompressed_continuous N κ).comp hl)

private theorem finitePhysical_zero_le_pi (N : ℕ) {κ : ℝ} (hκ : 0 < κ)
    {x : ℝ} (hx : x ≤ Real.pi) : finitePhysicalFeature N κ x = 0 := by
  by_cases he : x = Real.pi
  · subst x
    simp [finitePhysicalFeature, sourceOfProfile, Real.pi_ne_zero, finiteCompressed_zero N hκ]
  · have hn : ¬ Real.pi ≤ x := fun h => he (le_antisymm hx h)
    simp [finitePhysicalFeature, sourceOfProfile, hn]

private theorem finitePhysical_density_compact (N : ℕ) {κ : ℝ} (hκ : 0 < κ) (w : ℝ → ℝ) :
    HasCompactSupport (fun x : ℝ => w x * ‖finitePhysicalFeature N κ x‖ ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := Real.pi) (b := Real.pi * Real.exp (3 * κ / 4)))
  intro x hx
  by_contra h
  have hz : finitePhysicalFeature N κ x = 0 := by
    by_contra hn
    exact h (finitePhysical_support N hκ hn)
  exact hx (by simp [hz])

private theorem finitePhysical_mass_integrable (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => ‖finitePhysicalFeature N κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => ‖finitePhysicalFeature N κ x‖ ^ (2 : ℕ)) :=
    (finitePhysical_continuous N hκ).norm.pow 2
  have hs := finitePhysical_density_compact N hκ (fun _ : ℝ => 1)
  exact hc.integrable_of_hasCompactSupport (by simpa only [one_mul] using hs)

private theorem finitePhysical_sixth_integrable (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Integrable (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖finitePhysicalFeature N κ x‖ ^ 2) volume := by
  have hc : Continuous (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ) *
      ‖finitePhysicalFeature N κ x‖ ^ 2) :=
    ((continuous_id.div_const Real.pi).pow 6).mul
      ((finitePhysical_continuous N hκ).norm.pow 2)
  exact hc.integrable_of_hasCompactSupport
    (finitePhysical_density_compact N hκ (fun x : ℝ => (x / Real.pi) ^ (6 : ℕ)))

private theorem finitePhysical_h6 (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    originalPhysicalH6 (finitePhysicalFeature N κ) := by
  refine ⟨?_, (finitePhysical_sixth_integrable N hκ).integrableOn⟩
  exact ((finitePhysical_continuous N hκ).memLp_of_hasCompactSupport
    (finitePhysical_compact N hκ)).mono_measure Measure.restrict_le_self

private theorem finitePhysical_mass_Ioi_eq (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) =
      ∫ x : ℝ, ‖finitePhysicalFeature N κ x‖ ^ 2 := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioi Real.pi
  · simp [hx]
  · have hz := finitePhysical_zero_le_pi N hκ (le_of_not_gt hx)
    simp [hx, hz]

private theorem finitePhysical_mass_pos (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < ∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2 := by
  rw [finitePhysical_mass_Ioi_eq N hκ]
  apply integral_pos_of_integrable_nonneg_nonzero
    ((finitePhysical_continuous N hκ).norm.pow 2) (finitePhysical_mass_integrable N hκ)
    (fun x => sq_nonneg _) (x := Real.pi * Real.exp (κ / 2))
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (finitePhysical_center_ne N hκ))

private theorem finitePhysical_cap_bound (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    (∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) * ‖finitePhysicalFeature N κ x‖ ^ 2) ≤
      Real.exp (9 * κ / 2) *
        (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) := by
  rw [← integral_const_mul]
  apply integral_mono (finitePhysical_sixth_integrable N hκ).integrableOn
    ((finitePhysical_mass_integrable N hκ).const_mul _).integrableOn
  intro x
  by_cases hz : finitePhysicalFeature N κ x = 0
  · simp [hz]
  · have hx := finitePhysical_support N hκ hz
    have ha : 0 ≤ x / Real.pi :=
      div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ Real.exp (3 * κ / 4) := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      simpa only [mul_comm] using hx.2
    have hc := pow_le_pow_left₀ ha hb 6
    have he : Real.exp (3 * κ / 4) ^ (6 : ℕ) = Real.exp (9 * κ / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      <;> ring
    rw [he] at hc
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

private theorem finitePhysical_norm_le (N : ℕ) (κ x : ℝ) :
    ‖finitePhysicalFeature N κ x‖ ≤ 1 := by
  by_cases hx : Real.pi ≤ x
  · have hx1 : 1 ≤ x := by linarith [Real.one_le_pi_div_two]
    have hp0 : 0 ≤ x ^ (-9 / 4 : ℝ) := Real.rpow_nonneg (by linarith [Real.pi_pos]) _
    have hp1 : x ^ (-9 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    simp only [finitePhysicalFeature, sourceOfProfile, if_pos hx, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp0, finiteCompressedProfile]
    exact (mul_le_mul_of_nonneg_left (finiteProfile_norm_le N _) hp0).trans
      (by simpa only [mul_one] using hp1)
  · simp only [finitePhysicalFeature, sourceOfProfile, if_neg hx, norm_zero]
    norm_num

private theorem finitePhysical_support_four (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Function.support (finitePhysicalFeature N κ) ⊆ Icc Real.pi (4 * Real.pi) := by
  intro x hx
  refine ⟨(finitePhysical_support N hκ hx).1, ?_⟩
  by_contra h
  exact hx (finitePhysical_zero_high N hκ hκ1 (le_of_not_ge h))

private theorem finitePhysical_mass_upper (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) ≤ 3 * Real.pi := by
  rw [finitePhysical_mass_Ioi_eq N hκ]
  have hs : (∫ x : ℝ in Icc Real.pi (4 * Real.pi),
      ‖finitePhysicalFeature N κ x‖ ^ 2) =
        ∫ x : ℝ, ‖finitePhysicalFeature N κ x‖ ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : finitePhysicalFeature N κ x = 0 := by
        by_contra hh
        exact hx (finitePhysical_support_four N hκ hκ1 hh)
      simp only [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)])
  rw [← hs]
  calc
    _ ≤ ∫ x : ℝ in Icc Real.pi (4 * Real.pi), (1 : ℝ) := by
      apply integral_mono (finitePhysical_mass_integrable N hκ).integrableOn
        (integrableOn_const (by simp [Real.volume_Icc]))
      intro x
      have hnorm := finitePhysical_norm_le N κ x
      nlinarith [norm_nonneg (finitePhysicalFeature N κ x)]
    _ = 3 * Real.pi := by
      rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
        max_eq_left (by linarith [Real.pi_pos])]
      ring

private def finiteGammaEnergy (N : ℕ) (κ : ℝ) : ℝ :=
  ∫ ξ : ℝ, Symbol.gammaWeight ξ *
    ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2

private def finiteScaledBand (κ : ℝ) (n : ℕ) : Set ℝ :=
  Icc ((frequency n - 1) / κ) ((frequency n + 1) / κ)

private theorem finiteScaledBand_mem {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    {ξ : ℝ} (hξ : ξ ∈ finiteScaledBand κ n) : κ * ξ ∈ positiveBand n := by
  have ha := (div_le_iff₀ hκ).mp hξ.1
  have hb := (le_div_iff₀ hκ).mp hξ.2
  change κ * ξ ∈ Icc (frequency n - 1) (frequency n + 1)
  constructor <;> nlinarith [ha, hb]

private theorem finiteScaledBands_disjoint {κ : ℝ} (hκ : 0 < κ) :
    Pairwise (Disjoint on finiteScaledBand κ) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ξ hn hm
  exact Set.disjoint_left.mp (positiveBands_disjoint hnm)
    (finiteScaledBand_mem hκ n hn) (finiteScaledBand_mem hκ m hm)

private theorem finiteGammaEnergy_lower (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ((N + 1 : ℕ) : ℝ) * κ / (2048 * Real.pi * Symbol.domainConstant) ≤
      finiteGammaEnergy N κ := by
  let f : ℝ → ℝ := fun ξ => Symbol.gammaWeight ξ *
    ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖ ^ 2
  let b : ℝ := κ / (2048 * Real.pi * Symbol.domainConstant)
  let d : ℝ := κ ^ 2 / (4096 * Real.pi * Symbol.domainConstant)
  have hC : 0 < Symbol.domainConstant := by unfold Symbol.domainConstant; positivity
  have hf : Integrable f volume := finiteCompressed_gamma_integrable N hκ
  have hf0 (ξ : ℝ) : 0 ≤ f ξ := by
    have hp := (Symbol.actualGammaWeight_bounds ξ).1
    exact mul_nonneg (by linarith [hp]) (sq_nonneg _)
  have hband (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      b ≤ ∫ ξ : ℝ in finiteScaledBand κ n, f ξ := by
    have hpoint (ξ : ℝ) (hξ : ξ ∈ finiteScaledBand κ n) : d ≤ f ξ := by
      have hl := finiteCompressed_band_density_lower N n hn hκ hκ1
        (finiteScaledBand_mem hκ n hξ)
      have hc := mul_le_mul_of_nonneg_right
        (Symbol.actualGammaWeight_bounds ξ).2
        (sq_nonneg ‖unitarySourceFourier (finiteCompressedProfile N κ) ξ‖)
      dsimp [d, f]
      apply (div_le_iff₀ (by positivity : 0 < 4096 * Real.pi * Symbol.domainConstant)).mpr
      have hmul := mul_le_mul_of_nonneg_left (hl.trans (by simpa only [mul_assoc] using hc))
        (show 0 ≤ 4096 * Real.pi by positivity)
      field_simp [Real.pi_ne_zero] at hmul
      nlinarith [hmul]
    calc
      b = ∫ ξ : ℝ in finiteScaledBand κ n, d := by
        rw [setIntegral_const, finiteScaledBand, Real.volume_real_Icc, smul_eq_mul]
        have hw : (frequency n + 1) / κ - (frequency n - 1) / κ = 2 / κ := by ring
        rw [hw, max_eq_left (by positivity)]
        dsimp [b, d]
        field_simp [hκ.ne', hC.ne', Real.pi_ne_zero] <;> ring
      _ ≤ ∫ ξ : ℝ in finiteScaledBand κ n, f ξ := by
        apply integral_mono_ae (integrableOn_const (by simp [finiteScaledBand, Real.volume_Icc]))
          hf.integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with ξ hξ
        exact hpoint ξ hξ
  have hdis : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) (finiteScaledBand κ) :=
    fun n hn m hm hnm => finiteScaledBands_disjoint hκ hnm
  have hsum := integral_biUnion_finset (Finset.range (N + 1))
    (fun n hn => (show MeasurableSet (finiteScaledBand κ n) from measurableSet_Icc))
    hdis (fun n hn => hf.integrableOn (s := finiteScaledBand κ n))
  calc
    ((N + 1 : ℕ) : ℝ) * κ / (2048 * Real.pi * Symbol.domainConstant) =
        ∑ n ∈ Finset.range (N + 1), b := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      dsimp [b]
      ring
    _ ≤ ∑ n ∈ Finset.range (N + 1), ∫ ξ : ℝ in finiteScaledBand κ n, f ξ :=
      Finset.sum_le_sum hband
    _ = ∫ ξ : ℝ in ⋃ n ∈ Finset.range (N + 1), finiteScaledBand κ n, f ξ := hsum.symm
    _ ≤ finiteGammaEnergy N κ :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hf0) hf

private theorem finitePhysical_H6_tail (N : ℕ) {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    (∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) *
      ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2) ≤
        12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1) := by
  let f : ℝ → ℝ := fun x => (x / Real.pi) ^ (6 : ℕ) *
    ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2
  let r : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hz (x : ℝ) (hx : x ∉ Icc Real.pi (4 * Real.pi)) : f x = 0 := by
    by_cases hπ : Real.pi ≤ x
    · have hh : 4 * Real.pi ≤ x := by
        by_contra h
        exact hx ⟨hπ, le_of_lt (lt_of_not_ge h)⟩
      simp only [f, compressedFeature_zero_high hκ hκ1 hh,
        finitePhysical_zero_high N hκ hκ1 hh, sub_self, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    · simp only [f, compressedFeature, finitePhysicalFeature, sourceOfProfile,
        if_neg hπ, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  have hc : Continuous f := by
    dsimp [f]
    exact ((continuous_id.div_const Real.pi).pow 6).mul
      (((compressedFeature_continuous hκ).sub
        (finitePhysical_continuous N hκ)).norm.pow 2)
  have hs : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := Real.pi) (b := 4 * Real.pi))
    intro x hx
    by_contra h
    exact hx (hz x h)
  have hi : Integrable f volume := hc.integrable_of_hasCompactSupport hs
  have hf0 (x : ℝ) : 0 ≤ f x := by dsimp [f]; positivity
  have heq : (∫ x : ℝ in Icc Real.pi (4 * Real.pi), f x) = ∫ x : ℝ, f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hz
  have hpoint (x : ℝ) (hx : x ∈ Icc Real.pi (4 * Real.pi)) :
      f x ≤ 4096 * r ^ 2 := by
    have ha : 0 ≤ x / Real.pi := div_nonneg (le_trans Real.pi_pos.le hx.1) Real.pi_pos.le
    have hb : x / Real.pi ≤ 4 := (div_le_iff₀ Real.pi_pos).mpr hx.2
    have hw : (x / Real.pi) ^ (6 : ℕ) ≤ 4096 := by
      have h := pow_le_pow_left₀ ha hb 6
      norm_num at h
      exact h
    have ht := finitePhysical_uniform_tail N hκ x
    have ht2 := pow_le_pow_left₀
      (norm_nonneg (compressedFeature κ x - finitePhysicalFeature N κ x)) ht 2
    exact mul_le_mul hw ht2 (sq_nonneg _) (by norm_num)
  have hr2 : r ^ 2 = (1 / 4 : ℝ) ^ (N + 1) := by
    dsimp [r]
    calc
      ((1 / 2 : ℝ) ^ (N + 1)) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ (N + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm (N + 1) 2]
      _ = (1 / 4 : ℝ) ^ (N + 1) := by norm_num
  change (∫ x : ℝ in Ioi Real.pi, f x) ≤ _
  calc
    (∫ x : ℝ in Ioi Real.pi, f x) ≤ ∫ x : ℝ, f x :=
      integral_mono_measure Measure.restrict_le_self (Eventually.of_forall hf0) hi
    _ = ∫ x : ℝ in Icc Real.pi (4 * Real.pi), f x := heq.symm
    _ ≤ ∫ x : ℝ in Icc Real.pi (4 * Real.pi), 4096 * r ^ 2 := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const (by simp [Real.volume_Icc]))
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hpoint x hx
    _ = 12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1) := by
      rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul,
        max_eq_left (by linarith [Real.pi_pos]), hr2]
      ring

private theorem finitePhysical_H6_convergence {κ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    Tendsto (fun N : ℕ => ∫ x : ℝ in Ioi Real.pi,
      (x / Real.pi) ^ (6 : ℕ) *
        ‖compressedFeature κ x - finitePhysicalFeature N κ x‖ ^ 2)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 12288 * Real.pi * (1 / 4 : ℝ) ^ (N + 1))
      atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    simpa only [pow_succ, mul_zero, zero_mul] using
      (hpow.mul_const (1 / 4 : ℝ)).const_mul (12288 * Real.pi)
  apply squeeze_zero _ (fun N => finitePhysical_H6_tail N hκ hκ1) ht
  intro N
  apply integral_nonneg
  intro x
  positivity

/-- Finite actual Gamma energy has no upper bound relative to physical mass
inside any strict original H6 moment cap. Every witness belongs to every
constant-shift form domain. The same finite sources converge in actual H6
to a source outside every admissible constant-shift form domain. -/
theorem actual_h6_finite_gamma_energy_unbounded (K B : ℝ) (hK : 1 < K) :
    ∃ F : ℝ → ℂ,
      originalPhysicalH6 F ∧
      (∀ x : ℝ, (F x).im = 0) ∧
      (∀ x : ℝ, Real.pi ≤ x → HasSum (fun k : ℕ => physicalTerm F k x) (F x)) ∧
      (∀ c : ℝ, originalGammaFormDomain c F) ∧
      (0 < ∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) ∧
      ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖F x‖ ^ 2) <
        K * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2)) ∧
      (B * (∫ x : ℝ in Ioi Real.pi, ‖F x‖ ^ 2) <
        ∫ ξ : ℝ, Symbol.gammaWeight ξ *
          ‖unitarySourceFourier (actualGammaProfile F) ξ‖ ^ 2) ∧
      ∃ (F_limit : ℝ → ℂ) (G : ℕ → ℝ → ℂ),
        originalPhysicalH6 F_limit ∧
        (∀ c : ℝ, (∀ ξ : ℝ, 1 ≤ Symbol.gammaWeight ξ + c) →
          ¬ originalGammaFormDomain c F_limit) ∧
        (∀ n : ℕ, originalPhysicalH6 (G n) ∧
          (∀ x : ℝ, (G n x).im = 0) ∧
          (∀ x : ℝ, Real.pi ≤ x →
            HasSum (fun k : ℕ => physicalTerm (G n) k x) (G n x)) ∧
          (∀ c : ℝ, originalGammaFormDomain c (G n)) ∧
          (0 < ∫ x : ℝ in Ioi Real.pi, ‖G n x‖ ^ 2) ∧
          ((∫ x : ℝ in Ioi Real.pi, (x / Real.pi) ^ (6 : ℕ) * ‖G n x‖ ^ 2) <
            K * (∫ x : ℝ in Ioi Real.pi, ‖G n x‖ ^ 2))) ∧
        (∃ n : ℕ, F = G n) ∧
        Tendsto (fun n : ℕ => ∫ x : ℝ in Ioi Real.pi,
          (x / Real.pi) ^ (6 : ℕ) * ‖F_limit x - G n x‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨κ, hk, hkc, hkK⟩ := exists_cap_compression K hK
  have hk1 : κ ≤ 1 := by linarith
  have hC : 0 < Symbol.domainConstant := by unfold Symbol.domainConstant; positivity
  let D : ℝ := 2048 * Real.pi * Symbol.domainConstant
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max B 0 * (3 * Real.pi) * D / κ)
  have hNenergy : max B 0 * (3 * Real.pi) <
      ((N + 1 : ℕ) : ℝ) * κ / D := by
    have hm := (div_lt_iff₀ hk).mp hN
    apply (lt_div_iff₀ hD).mpr
    push_cast
    nlinarith [hm]
  have hmass := finitePhysical_mass_pos N hk
  have hupper := finitePhysical_mass_upper N hk hk1
  have henergy : B * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) <
      finiteGammaEnergy N κ := by
    calc
      B * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) ≤
          max B 0 * (∫ x : ℝ in Ioi Real.pi, ‖finitePhysicalFeature N κ x‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmass.le
      _ ≤ max B 0 * (3 * Real.pi) :=
        mul_le_mul_of_nonneg_left hupper (le_max_right _ _)
      _ < ((N + 1 : ℕ) : ℝ) * κ / D := hNenergy
      _ ≤ finiteGammaEnergy N κ := finiteGammaEnergy_lower N hk hk1
  refine ⟨finitePhysicalFeature N κ, finitePhysical_h6 N hk,
    finitePhysical_real N κ, ?_, ?_, hmass, ?_, ?_, ?_⟩
  · intro x hx
    exact finitePhysical_fullHasSum N hk hk1 hx
  · intro c
    exact finitePhysical_in_all_shift_domains N hk hk1 c
  · exact lt_of_le_of_lt (finitePhysical_cap_bound N hk)
      (mul_lt_mul_of_pos_right hkK hmass)
  · rw [finitePhysical_actualProfile_eq N hk hk1]
    exact henergy
  · refine ⟨compressedFeature κ, (fun n => finitePhysicalFeature n κ),
      compressed_original_h6 hk, ?_, ?_, ⟨N, rfl⟩, finitePhysical_H6_convergence hk hk1⟩
    · intro c hc
      exact compressed_not_form_domain hk hk1 c hc
    · intro n
      have hn_mass := finitePhysical_mass_pos n hk
      exact ⟨finitePhysical_h6 n hk, finitePhysical_real n κ,
        fun x hx => finitePhysical_fullHasSum n hk hk1 hx,
        fun c => finitePhysical_in_all_shift_domains n hk hk1 c,
        hn_mass, lt_of_le_of_lt (finitePhysical_cap_bound n hk)
          (mul_lt_mul_of_pos_right hkK hn_mass)⟩

end D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
