/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeFixedRatioWindowMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Each off-line zeta zero gives a prime-tail mass bound on fixed-ratio windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
import D5.S3.Weil.ZeroData.ActualHighZeroFilter
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.MeasureTheory.Integral.Prod

/-! Fixed-ratio windows for the negative mass of the actual prime-only Chebyshev tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.Mertens.WeightedPrimeLimit (chebyshev_error_kernel_integrable)
open D5.S3.Weil.Mertens.IntegratedExplicit (actualCoeff)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualFilteredLeadingPair (actual_filtered_leading_pair)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection
  (primeTail prime_integrable prime_power_window_correction)
open D5.S3.Weil.ZeroData.ActualHighZeroFilter (exists_actual_high_zero_filter)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open PositiveSpectralKernel (expMoment)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass

/-- A common forward probability average transfers signed mass to positive-part
mass on an interval containing all of the translates. -/
private theorem average_integral_le_positive_mass {f : ℝ → ℝ} {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {a b h l r : ℝ} (hν : ν (Icc 0 h) = 1)
    (hla : l ≤ a) (hab : a ≤ b) (hbr : b + h ≤ r)
    (hf : ContinuousOn f (Icc l r)) :
    IntervalIntegrable (fun t => ∫ s, f (t + s) ∂ν) volume a b ∧
      (∫ t in a..b, ∫ s, f (t + s) ∂ν) ≤ ∫ t in l..r, max (f t) 0 := by
  have hsupp : ∀ᵐ s ∂ν, s ∈ Icc 0 h :=
    (mem_ae_iff_prob_eq_one measurableSet_Icc).2 hν
  have hrestrict : ν.restrict (Icc 0 h) = ν := Measure.restrict_eq_self_of_ae_mem hsupp
  have hadd (t s : ℝ) (ht : t ∈ Icc a b) (hs : s ∈ Icc 0 h) : t + s ∈ Icc l r :=
    ⟨(hla.trans ht.1).trans (le_add_of_nonneg_right hs.1),
      (add_le_add ht.2 hs.2).trans hbr⟩
  have hprod : Integrable (Function.uncurry (fun t s : ℝ => f (t + s)))
      ((volume.restrict (uIoc a b)).prod ν) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => f (p.1 + p.2))
        (Icc a b ×ˢ Icc 0 h) :=
      hf.comp (by fun_prop) (fun p hp => hadd p.1 p.2 hp.1 hp.2)
    have hi := (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (μ := volume.prod ν)).mono_set
      (show uIoc a b ×ˢ Icc 0 h ⊆ Icc a b ×ˢ Icc 0 h from
        prod_mono (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self) Subset.rfl)
    rw [IntegrableOn, ← Measure.prod_restrict, hrestrict] at hi
    exact hi
  let mass := ∫ t in l..r, max (f t) 0
  have hpos : ContinuousOn (fun t => max (f t) 0) (Icc l r) :=
    hf.sup continuousOn_const
  have hshift : ∀ᵐ s ∂ν, (∫ t in a..b, f (t + s)) ≤ mass := by
    filter_upwards [hsupp] with s hs
    have hleft : l ≤ a + s := hla.trans (le_add_of_nonneg_right hs.1)
    have horder : a + s ≤ b + s := add_le_add_left hab s
    have hright : b + s ≤ r := (add_le_add_right hs.2 b).trans hbr
    have hsubset : Icc (a + s) (b + s) ⊆ Icc l r := Icc_subset_Icc hleft hright
    rw [intervalIntegral.integral_comp_add_right]
    calc
      _ ≤ ∫ t in a + s..b + s, max (f t) 0 :=
        intervalIntegral.integral_mono_on horder
          ((hf.mono hsubset).intervalIntegrable_of_Icc horder)
          ((hpos.mono hsubset).intervalIntegrable_of_Icc horder) (fun t _ => le_max_left _ _)
      _ ≤ mass := intervalIntegral.integral_mono_interval hleft horder hright
        (ae_of_all _ fun _ => le_max_right _ _)
        (hpos.intervalIntegrable_of_Icc (hleft.trans (horder.trans hright)))
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 ?_, ?_⟩
  · simpa only [IntegrableOn, uIoc_of_le hab, Function.uncurry] using hprod.integral_prod_left
  rw [intervalIntegral_integral_swap hprod]
  have houter : Integrable (fun s => ∫ t in a..b, f (t + s)) ν := by
    simpa only [uIoc_of_le hab, intervalIntegral.integral_of_le hab, Function.uncurry] using
      hprod.integral_prod_right
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae houter (integrable_const mass) hshift

/-- A fixed subinterval of each two-period window has cosine at least one half. -/
private theorem cosine_subinterval {γ : ℝ} (hγ : 0 < γ) (phase T : ℝ) :
    ∃ a : ℝ, T ≤ a ∧ a + (Real.pi / 3) / γ ≤ T + 2 * (2 * Real.pi / γ) ∧
      ∀ t ∈ Icc a (a + (Real.pi / 3) / γ), 1 / 2 ≤ Real.cos (γ * t + phase) := by
  let lag := toIcoMod Real.two_pi_pos 0 (-(γ * T + phase))
  let a := T + lag / γ
  let k := toIcoDiv Real.two_pi_pos 0 (-(γ * T + phase))
  have hlag : lag ∈ Ico 0 (2 * Real.pi) := toIcoMod_mem_Ico' Real.two_pi_pos _
  have ha : T ≤ a := le_add_of_nonneg_right (div_nonneg hlag.1 hγ.le)
  have hdecomp : lag + (k : ℝ) * (2 * Real.pi) = -(γ * T + phase) := by
    simpa only [lag, k, zsmul_eq_mul] using
      toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos 0 (-(γ * T + phase))
  have hlagmul : γ * (lag / γ) = lag := by rw [mul_comm, div_mul_cancel₀ _ hγ.ne']
  refine ⟨a, ha, ?_, ?_⟩
  · have hlag' := div_lt_div_of_pos_right hlag.2 hγ
    have hwidth := div_le_div_of_nonneg_right
      (show Real.pi / 3 ≤ 2 * Real.pi by linarith [Real.pi_pos]) hγ.le
    dsimp only [a]
    linarith only [hlag', hwidth]
  · intro t ht
    have hangle : γ * (t - a) ∈ Icc 0 (Real.pi / 3) := by
      refine ⟨mul_nonneg hγ.le (sub_nonneg.mpr ht.1), ?_⟩
      have ht' : t - a ≤ (Real.pi / 3) / γ := by linarith only [ht.2]
      calc
        _ ≤ γ * ((Real.pi / 3) / γ) := mul_le_mul_of_nonneg_left ht' hγ.le
        _ = _ := by rw [mul_comm, div_mul_cancel₀ _ hγ.ne']
    have hphase : γ * t + phase = γ * (t - a) + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [Int.cast_neg]
      dsimp only [a]
      linarith only [hdecomp, hlagmul]
    rw [hphase, Real.cos_add_int_mul_two_pi, ← Real.cos_pi_div_three]
    have hthird : Real.pi / 3 ∈ Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    exact Real.antitoneOn_cos ⟨hangle.1, hangle.2.trans hthird.2⟩ hthird hangle.2

private theorem prime_mass_from_log_mass {T U : ℝ} (hT : Real.log 2 ≤ T) (hTU : T ≤ U) :
    Real.exp (T / 2) * (∫ t in T..U, max (-Q (Real.exp t)) 0) ≤
      ∫ x in Real.exp T..Real.exp U, max (-primeTail x) 0 / Real.sqrt x := by
  have hx (t : ℝ) (ht : T ≤ t) : 1 ≤ Real.exp t :=
    Real.one_le_exp ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans (hT.trans ht))
  have hQ : ContinuousOn Q (Ici (1 : ℝ)) :=
    chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
  have hp : ContinuousOn primeTail (Ici (1 : ℝ)) :=
    prime_integrable.continuousOn_Ici_primitive_Ioi
  have hc : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Ici (1 : ℝ)) :=
    (hp.neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)).ne')
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := T) (b := U) (f := Real.exp) (f' := Real.exp)
    (g := fun x => max (-primeTail x) 0 / Real.sqrt x) (fun t _ => Real.hasDerivAt_exp t)
    Real.continuous_exp.continuousOn (hc.mono (by
      rintro _ ⟨t, ht, rfl⟩
      rw [uIcc_of_le hTU] at ht
      exact hx t ht.1))
  have hmaps : MapsTo Real.exp (Icc T U) (Ici (1 : ℝ)) := fun t ht => hx t ht.1
  have hleft : ContinuousOn (fun t => Real.exp (T / 2) * max (-Q (Real.exp t)) 0) (Icc T U) :=
    continuousOn_const.mul
      ((hQ.comp Real.continuous_exp.continuousOn hmaps).neg.sup continuousOn_const)
  have hright : ContinuousOn (fun t => (max (-primeTail (Real.exp t)) 0 /
      Real.sqrt (Real.exp t)) * Real.exp t) (Icc T U) :=
    (hc.comp Real.continuous_exp.continuousOn hmaps).mul Real.continuous_exp.continuousOn
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hcorrection := (prime_power_window_correction.2 C (fun x _ => hC x)).1
  rw [← hsubst, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hTU (hleft.intervalIntegrable_of_Icc hTU)
    (hright.intervalIntegrable_of_Icc hTU)
  intro t ht
  have hs : 0 < Real.sqrt (Real.exp t) := Real.sqrt_pos.mpr (Real.exp_pos t)
  have hroot : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hweight : Real.exp (T / 2) ≤ Real.sqrt (Real.exp t) := by
    rw [hroot]
    exact Real.exp_le_exp.mpr (by linarith only [ht.1])
  have htail : primeTail (Real.exp t) ≤ Q (Real.exp t) :=
    sub_nonneg.mp (hcorrection _ (hx t ht.1)).1
  calc
    _ ≤ Real.sqrt (Real.exp t) * max (-primeTail (Real.exp t)) 0 :=
      mul_le_mul hweight (max_le_max (neg_le_neg htail) le_rfl) (le_max_right _ _) hs.le
    _ = _ := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hs.ne').2
      rw [mul_right_comm, ← sq, Real.sq_sqrt (Real.exp_nonneg t), mul_comm]

/-- Every actual nontrivial zero to the right of the critical line gives a fixed
ratio and an eventual lower mass bound at the exponent of its own real part. -/
theorem prime_tail_fixed_ratio_mass_of_zero (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    let β := ρ.re
    1 / 2 < β → ∃ κ c S : ℝ, 1 < κ ∧ 0 < c ∧ ∀ B : ℝ, S ≤ B → ∀ A : ℝ, 2 ≤ A →
      κ * A ≤ B → c * B ^ (β - 1 / 2) ≤
        ∫ x in A..B, max (-primeTail x) 0 / Real.sqrt x := by
  change 1 / 2 < ρ.re → _
  intro hβ
  classical
  let occurrence (n : ℕ) : ℕ :=
    actualOccurrenceEquiv.symm ⟨n, ⟨0, actualData.multiplicity_pos n⟩⟩
  have hoccurrence (n : ℕ) : actualZero (occurrence n) = actualData.zero n := by
    simp only [actualZero, occurrence, Equiv.apply_symm_apply]
  obtain ⟨n, hn⟩ := actualData.zero_exhaustive hρ
  have hheight (z : ℂ) (hz : IsNontrivialZero z) : z.im ≠ 0 := by
    intro h
    have hh := actual_height_gt_ten z hz
    rw [h, abs_zero] at hh
    norm_num at hh
  obtain ⟨p, hpβ, hpγ⟩ : ∃ p : ℕ, (actualZero p).re = ρ.re ∧ 0 < (actualZero p).im := by
    rcases lt_or_gt_of_ne (hheight ρ hρ) with hneg | hpos
    · refine ⟨occurrence (actualData.conjugation n), ?_, ?_⟩
      · simp [hoccurrence, actualData.zero_conjugation, hn]
      · simpa [hoccurrence, actualData.zero_conjugation, hn] using hneg
    · exact ⟨occurrence n, by rw [hoccurrence, hn], by simpa [hoccurrence, hn] using hpos⟩
  let z := actualZero p
  let σ : ℝ := (1 / 2 + z.re) / 2
  have hσ : 1 / 2 < σ := by dsimp [σ, z]; linarith only [hpβ, hβ]
  have hσz : σ < z.re := by dsimp [σ, z]; linarith only [hpβ, hβ]
  obtain ⟨ν, hνprob, hν, hfilter, hmoment⟩ :=
    exists_actual_high_zero_filter hσ (H := 0) le_rfl p hpγ
  let _ : IsProbabilityMeasure ν := hνprob
  have hkill (j : ℕ) (hj : σ < (actualZero j).re) (hjp : actualZero j ≠ z)
      (hjc : actualZero j ≠ conj z) : expMoment ν (actualZero j - 1) = 0 := by
    have hj0 := hheight (actualZero j)
      (actualData.zero_isNontrivial (actualOccurrenceEquiv j).1)
    rcases lt_or_gt_of_ne hj0 with hneg | hpos
    · let k := occurrence (actualData.conjugation (actualOccurrenceEquiv j).1)
      have hk : actualZero k = conj (actualZero j) := by
        rw [hoccurrence, actualData.zero_conjugation]
        rfl
      have hkj : σ < (actualZero k).re := by simpa [hk] using hj
      have hkp : 0 < (actualZero k).im := by simpa [hk] using hneg
      have hkne : actualZero k ≠ z := by
        intro he
        apply hjc
        simpa [hk] using congrArg (fun w : ℂ => conj w) he
      simpa [hk] using (hfilter k hkj hkp hkne).2
    · exact (hfilter j hj hpos hjp).1
  let h : ℝ := ∑' j : ℕ, if σ < (actualZero j).re ∧ 0 < (actualZero j).im ∧
    actualZero j ≠ z then 2 * Real.pi / (actualZero j).im else 0
  have hνh : ν (Icc 0 h) = 1 := hν
  let a := actualCoeff p * expMoment ν (z - 1)
  let C : ℝ := 2 * (analyticOrderNatAt riemannZeta z : ℝ) * ‖a‖
  let E : ℝ := (∑' k : ℕ, ‖actualCoeff k‖) + Real.log (2 * Real.pi)
  have hpair := actual_filtered_leading_pair ν p hνh (by linarith only [hσ]) hσz hpγ hmoment hkill
  change a ≠ 0 ∧ 0 < C ∧ σ - 1 < z.re - 1 ∧ 0 ≤ E ∧
    ∃ R : ℝ → ℝ, ∀ t : ℝ, Real.log 2 ≤ t →
      (∫ s : ℝ, Q (Real.exp (t + s)) ∂ν) =
        -(C * Real.exp ((z.re - 1) * t) * Real.cos (z.im * t + a.arg)) + R t ∧
      |R t| ≤ E * Real.exp ((σ - 1) * t) at hpair
  obtain ⟨_, hC, _, _, R, hR⟩ := hpair
  have hlimit : Tendsto (fun t : ℝ => E * Real.exp ((σ - z.re) * t)) atTop (𝓝 0) := by
    have hdecay := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (sub_neg.mpr hσz))
    simpa only [Function.comp_def, id_eq, mul_zero] using hdecay.const_mul E
  obtain ⟨T₀, hsmall⟩ := eventually_atTop.mp
    (hlimit.eventually_lt_const (show 0 < C / 4 by positivity))
  have hneg : z.re - 1 ≤ 0 := sub_nonpos.mpr
    (actualData.zero_isNontrivial (actualOccurrenceEquiv p).1).2.2.le
  let P := 2 * Real.pi / z.im
  let L := (Real.pi / 3) / z.im
  let W := 2 * P + max h 0
  have hP : 0 < P := div_pos Real.two_pi_pos hpγ
  have hL : 0 < L := div_pos (by positivity) hpγ
  have hW : 0 < W := by dsimp only [W]; linarith [le_max_right h 0]
  let d := L * (C / 4 * Real.exp ((z.re - 1) * (2 * P)))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hlogmass (T : ℝ) (hT : Real.log 2 ≤ T) (hT₀ : T₀ ≤ T) :
      d * Real.exp ((z.re - 1) * T) ≤
        ∫ t in T..T + W, max (-Q (Real.exp t)) 0 := by
    obtain ⟨u, hu, huv, hcos⟩ := cosine_subinterval hpγ a.arg T
    change u + L ≤ T + 2 * P at huv
    have hordered : u ≤ u + L := le_add_of_nonneg_right hL.le
    have hW' : u + L + h ≤ T + W := by
      dsimp only [W]
      linarith only [huv, le_max_left h 0]
    let f := fun t : ℝ => -Q (Real.exp t)
    have hQ : ContinuousOn Q (Ici (1 : ℝ)) :=
      chebyshev_error_kernel_integrable.continuousOn_Ici_primitive_Ioi
    have hf : ContinuousOn f (Icc T (T + W)) :=
      (hQ.comp Real.continuous_exp.continuousOn (fun t ht =>
        Real.one_le_exp ((Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)).trans
          (hT.trans ht.1)))).neg
    have havg (t : ℝ) (ht : t ∈ Icc u (u + L)) :
        C / 4 * Real.exp ((z.re - 1) * (T + 2 * P)) ≤ ∫ s, f (t + s) ∂ν := by
      have hTt := hu.trans ht.1
      obtain ⟨hformula, herror⟩ := hR t (hT.trans hTt)
      have hexp : Real.exp ((σ - 1) * t) =
          Real.exp ((σ - z.re) * t) * Real.exp ((z.re - 1) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp, ← mul_assoc] at herror
      have herr := herror.trans (mul_le_mul_of_nonneg_right
        (hsmall t (hT₀.trans hTt)).le (Real.exp_nonneg _))
      have hcos' := mul_le_mul_of_nonneg_left (hcos t ht)
        (mul_nonneg hC.le (Real.exp_nonneg ((z.re - 1) * t)))
      have hscale := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (ht.2.trans huv) hneg))
        (show 0 ≤ C / 4 by positivity)
      change _ ≤ ∫ s, -Q (Real.exp (t + s)) ∂ν
      rw [integral_neg, hformula]
      linarith only [hscale, hcos', (abs_le.mp herr).2]
    obtain ⟨havgInt, htransfer⟩ := average_integral_le_positive_mass hνh hu hordered hW' hf
    calc
      _ = ∫ _ in u..u + L, C / 4 * Real.exp ((z.re - 1) * (T + 2 * P)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left, mul_add, Real.exp_add]
        dsimp only [d]
        ring
      _ ≤ ∫ t in u..u + L, ∫ s, f (t + s) ∂ν :=
        intervalIntegral.integral_mono_on hordered intervalIntegrable_const havgInt havg
      _ ≤ _ := htransfer
  let τ := max (Real.log 2) T₀
  let κ := Real.exp W
  let c := d * Real.exp (-(z.re - 1 / 2) * W)
  have hκ : 1 < κ := Real.one_lt_exp_iff.mpr hW
  have hc : 0 < c := mul_pos hd (Real.exp_pos _)
  refine ⟨κ, c, Real.exp (τ + W), hκ, hc, ?_⟩
  intro B hB A hA hratio
  have hB₀ : 0 < B := (Real.exp_pos _).trans_le hB
  let T := Real.log B - W
  have hτ : τ ≤ T := by
    have hh := Real.log_le_log (Real.exp_pos _) hB
    rw [Real.log_exp] at hh
    dsimp only [T]
    linarith only [hh]
  have hT : Real.log 2 ≤ T := (le_max_left _ _).trans hτ
  have hT₀ : T₀ ≤ T := (le_max_right _ _).trans hτ
  have hTU : T ≤ T + W := le_add_of_nonneg_right hW.le
  have hright : Real.exp (T + W) = B := by
    dsimp only [T]
    rw [sub_add_cancel, Real.exp_log hB₀]
  have hleft : A ≤ Real.exp T := by
    change A ≤ Real.exp (Real.log B - W)
    rw [Real.exp_sub, Real.exp_log hB₀]
    exact (le_div_iff₀ (Real.exp_pos W)).2 (by simpa only [mul_comm] using hratio)
  have hTB : Real.exp T ≤ B := hright ▸ Real.exp_le_exp.mpr hTU
  have hlower := mul_le_mul_of_nonneg_left (hlogmass T hT hT₀) (Real.exp_nonneg (T / 2))
  have hweight := (hlower.trans (prime_mass_from_log_mass hT hTU))
  rw [hright] at hweight
  have hm : ContinuousOn (fun x => max (-primeTail x) 0 / Real.sqrt x) (Icc A B) := by
    have hx (x : ℝ) (hm : x ∈ Icc A B) : 1 ≤ x :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (hA.trans hm.1)
    have hc : ContinuousOn primeTail (Ici (1 : ℝ)) :=
      prime_integrable.continuousOn_Ici_primitive_Ioi
    exact ((hc.mono hx).neg.sup continuousOn_const).div Real.continuous_sqrt.continuousOn
      (fun x hm => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx x hm))).ne')
  calc
    _ = Real.exp (T / 2) * (d * Real.exp ((z.re - 1) * T)) := by
      rw [Real.rpow_def_of_pos hB₀, ← hpβ]
      have he : -(z.re - 1 / 2) * W + Real.log B * (z.re - 1 / 2) =
          T / 2 + (z.re - 1) * T := by dsimp only [T]; ring
      dsimp only [c]
      rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
      ring
    _ ≤ ∫ x in Real.exp T..B, max (-primeTail x) 0 / Real.sqrt x := hweight
    _ ≤ _ := intervalIntegral.integral_mono_interval hleft hTB le_rfl
      (ae_of_all _ fun x => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg x))
      (hm.intervalIntegrable_of_Icc (hleft.trans hTB))

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeFixedRatioWindowMass
