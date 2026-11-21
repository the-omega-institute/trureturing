/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePrescribedRatioWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePrescribedRatioWindowMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An unattained zeta abscissa gives prime-tail mass on every prescribed ratio. -/

import D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

/-! An arbitrarily short filter and a sufficiently rapid retained oscillation
fit together in each prescribed logarithmic window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.Analytic.ActualUnattainedAbscissaFilter (exists_dominant_actual_zero_filter)
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair (actual_filtered_leading_pair)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
  (average_integral_le_positive_mass cosine_subinterval prime_mass_from_log_mass)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail prime_integrable)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero actualData actualOccurrenceEquiv)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass

/-- Below an unattained zeta abscissa, each surplus exponent gives an eventual
prime-tail negative mass bound for every window of the prescribed ratio. -/
theorem prime_tail_prescribed_ratio_mass_of_unattained :
    let belowAbscissa := Iio zeroAbscissa
    (∀ z : ℂ, IsNontrivialZero z → z.re ∈ belowAbscissa) →
      ∀ {κ σ : ℝ}, 1 < κ → 1 / 2 < σ → σ ∈ belowAbscissa →
        ∃ c S : ℝ, 0 < c ∧ ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A →
          κ * A ≤ B → c * B ^ (σ - 1 / 2) ≤
            ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x := by
  dsimp only
  intro hun κ σ hκ hσ hσΘ
  let W := Real.log κ
  let h := W / 2
  have hW : 0 < W := Real.log_pos hκ
  have hh : 0 < h := half_pos hW
  obtain ⟨p, b, ν, hγ, hfast, hσb, hbβ, hprob, hmass, hkill, hkeep⟩ :=
    exists_dominant_actual_zero_filter hσ hσΘ hh (F := 4 * Real.pi / h) hun
  let _ : IsProbabilityMeasure ν := hprob
  let ρ := actualZero p
  let P := 2 * Real.pi / ρ.im
  let L := (Real.pi / 3) / ρ.im
  have hL : 0 < L := div_pos (by positivity) hγ
  have hfit : h + 2 * P < W := by
    have hγh : 4 * Real.pi < ρ.im * h := (div_lt_iff₀ hh).mp hfast
    have hP : 2 * P < h := by
      dsimp only [P]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hγ).2
      change 2 * (2 * Real.pi) < h * ρ.im
      linarith only [mul_comm h ρ.im, hγh]
    dsimp only [h] at hP ⊢
    linarith only [hP]
  have hb₀ : 0 ≤ b := by linarith only [hσ, hσb]
  let a := actualCoeff p * PositiveSpectralKernel.expMoment ν (ρ - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖a‖
  let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
  have hpair := actual_filtered_leading_pair ν p hmass hb₀ hbβ hγ hkeep hkill
  change a ≠ 0 ∧ 0 < C ∧ b - 1 < ρ.re - 1 ∧ 0 ≤ E ∧
    ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
      (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
        -(C * Real.exp ((ρ.re - 1) * t) * Real.cos (ρ.im * t + a.arg)) + R t ∧
      |R t| ≤ E * Real.exp ((b - 1) * t) at hpair
  obtain ⟨_, hC, _, _, R, hR⟩ := hpair
  have hneg : ρ.re - 1 ≤ 0 :=
    sub_nonpos.mpr (actualData.zero_isNontrivial (actualOccurrenceEquiv p).1).2.2.le
  have hlimit : Tendsto (fun t : ℝ => E * Real.exp ((b - ρ.re) * t)) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hbβ))
    simpa only [Function.comp_def, id_eq, mul_zero] using hdecay.const_mul E
  obtain ⟨T₀, hsmall⟩ := eventually_atTop.mp
    (hlimit.eventually_lt_const (show 0 < C / 4 by positivity))
  let d := L * (C / 4 * Real.exp ((ρ.re - 1) * (2 * P)))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hlogmass (T : ℝ) (hT : Real.log 2 ≤ T) (hT₀ : T₀ ≤ T) :
      d * Real.exp ((ρ.re - 1) * T) ≤
        ∫ t in T..T + W, max (-Q (Real.exp t)) 0 := by
    obtain ⟨u, hu, huv, hcos⟩ := cosine_subinterval hγ a.arg T
    change u + L ≤ T + 2 * P at huv
    have hordered : u ≤ u + L := le_add_of_nonneg_right hL.le
    have htranslate : u + L + h ≤ T + W := by linarith only [huv, hfit]
    let f := fun t : ℝ => -Q (Real.exp t)
    have hQ : ContinuousOn Q (Ici (1 : ℝ)) :=
      chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
    have hf : ContinuousOn f (Icc T (T + W)) :=
      (hQ.comp Real.continuous_exp.continuousOn (fun t ht =>
        Real.one_le_exp ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans
          (hT.trans ht.1)))).neg
    have havg (t : ℝ) (ht : t ∈ Icc u (u + L)) :
        C / 4 * Real.exp ((ρ.re - 1) * (T + 2 * P)) ≤ ∫ s, f (t + s) ∂ν := by
      have hTt := hu.trans ht.1
      obtain ⟨hformula, herror⟩ := hR t (hT.trans hTt)
      have hexp : Real.exp ((b - 1) * t) =
          Real.exp ((b - ρ.re) * t) * Real.exp ((ρ.re - 1) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, ← mul_assoc] at herror
      have herr := herror.trans (mul_le_mul_of_nonneg_right
        (hsmall t (hT₀.trans hTt)).le (Real.exp_nonneg _))
      have hcos' := mul_le_mul_of_nonneg_left (hcos t ht)
        (mul_nonneg hC.le (Real.exp_nonneg ((ρ.re - 1) * t)))
      have hscale := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (ht.2.trans huv) hneg))
        (show 0 ≤ C / 4 by positivity)
      change _ ≤ ∫ s, -Q (Real.exp (t + s)) ∂ν
      rw [integral_neg, hformula]
      linarith only [hscale, hcos', (abs_le.mp herr).2]
    obtain ⟨havgInt, htransfer⟩ :=
      average_integral_le_positive_mass hmass hu hordered htranslate hf
    calc
      _ = ∫ _ in u..u + L, C / 4 * Real.exp ((ρ.re - 1) * (T + 2 * P)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_add, Real.exp_add]
        dsimp only [d]
        ring
      _ ≤ ∫ t in u..u + L, ∫ s, f (t + s) ∂ν :=
        intervalIntegral.integral_mono_on hordered intervalIntegrable_const havgInt havg
      _ ≤ _ := htransfer
  let τ := max (Real.log 2) T₀
  let c := d * Real.exp (-(ρ.re - 1 / 2) * W)
  have hc : 0 < c := mul_pos hd (Real.exp_pos _)
  refine ⟨c, Real.exp (τ + W), hc, ?_⟩
  intro B hB A hA hratio
  have hB₀ : 0 < B := (Real.exp_pos _).trans_le hB
  let T := Real.log B - W
  have hτ : τ ≤ T := by
    have hlog := Real.log_le_log (Real.exp_pos _) hB
    rw [Real.log_exp] at hlog
    exact le_sub_iff_add_le.mpr hlog
  have hT : Real.log 2 ≤ T := (le_max_left _ _).trans hτ
  have hT₀ : T₀ ≤ T := (le_max_right _ _).trans hτ
  have hTU : T ≤ T + W := le_add_of_nonneg_right hW.le
  have hright : Real.exp (T + W) = B := by
    dsimp only [T]
    rw [sub_add_cancel, Real.exp_log hB₀]
  have hleft : A ≤ Real.exp T := by
    change A ≤ Real.exp (Real.log B - Real.log κ)
    rw [Real.exp_sub, Real.exp_log hB₀, Real.exp_log (zero_lt_one.trans hκ)]
    exact (le_div_iff₀ (zero_lt_one.trans hκ)).2 (by simpa only [mul_comm] using hratio)
  have hTB : Real.exp T ≤ B := hright ▸ Real.exp_le_exp.mpr hTU
  have hB₁ : 1 ≤ B := one_le_two.trans (hA.trans (hleft.trans hTB))
  have hweight := (mul_le_mul_of_nonneg_left (hlogmass T hT hT₀) (Real.exp_nonneg (T / 2))).trans
    (prime_mass_from_log_mass hT hTU)
  rw [hright] at hweight
  have hx (x : ℝ) (hmem : x ∈ Icc A B) : 1 ≤ x := one_le_two.trans (hA.trans hmem.1)
  have hm : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Icc A B) :=
    ((prime_integrable.continuousOn_Ici_primitive_Ioi.mono hx).neg.sup continuousOn_const).div
      Real.continuous_sqrt.continuousOn
      (fun x hmem => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx x hmem))).ne')
  calc
    _ ≤ c * B ^ (ρ.re - 1 / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hB₁ (sub_le_sub_right (hσb.trans hbβ.le) _)) hc.le
    _ = Real.exp (T / 2) * (d * Real.exp ((ρ.re - 1) * T)) := by
      rw [Real.rpow_def_of_pos hB₀]
      have he : -(ρ.re - 1 / 2) * W + Real.log B * (ρ.re - 1 / 2) =
          T / 2 + (ρ.re - 1) * T := by dsimp only [T]; ring
      dsimp only [c]
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
      ring
    _ ≤ ∫ x in Real.exp T..B, max (-primeTail x) 0 / Real.sqrt x := hweight
    _ ≤ _ := intervalIntegral.integral_mono_interval hleft hTB le_rfl
      (ae_of_all _ fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x))
      (hm.intervalIntegrable_of_Icc (hleft.trans hTB))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePrescribedRatioWindowMass
