/- GID: D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineIntegralMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Fourier.LpSpace]
   utility: none
   digest: The actual cosine-integral tail has its exact complex Lebesgue L2 Fourier multiplier at every positive scale. -/

import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open scoped Topology FourierTransform
open D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)

namespace D5.S3.Fourier.Asymptotics.CosineIntegralMultiplier

/-- The complex-valued spatial cosine-integral kernel. -/
noncomputable def q (c x : ℝ) : ℂ := (2 * cosineIntegral (c * |x|) : ℝ)
/-- The frequency multiplier for the phase exp(-2 pi i x xi). -/
noncomputable def m (c ξ : ℝ) : ℂ := (if c / (2 * Real.pi) ≤ |ξ| then -1 / |ξ| else 0 : ℝ)

/-- The exact Fourier transform of the actual cosine-integral tail in complex Lebesgue L2. -/
theorem result (c : ℝ) (hc : 0 < c) :
    ∃ hq : MemLp (q c) 2 volume, ∃ hm : MemLp (m c) 2 volume,
      Lp.fourierTransformₗᵢ ℝ ℂ (hq.toLp (q c)) = hm.toLp (m c) := by
  -- Measurability uses the actual parameter-dependent sine-tail integral.
  have hCmeas : Measurable cosineIntegral := by
    have htail : StronglyMeasurable (fun x : ℝ => ∫ t in Ioi x, Real.sin t / t ^ 2) := by
      have heq : (fun x : ℝ => ∫ t in Ioi x, Real.sin t / t ^ 2) =
          fun x => ∫ t : ℝ, if x < t then Real.sin t / t ^ 2 else 0 := by
        funext x
        rw [← integral_indicator measurableSet_Ioi]
        rfl
      rw [heq]
      apply StronglyMeasurable.integral_prod_right
      apply Measurable.stronglyMeasurable
      exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        ((Real.measurable_sin.comp measurable_snd).div (measurable_snd.pow_const 2))
        measurable_const
    exact (Real.measurable_sin.div measurable_id).sub htail.measurable
  have hq (a : ℝ) (ha : 0 < a) : MemLp (q a) 2 volume := by
    have hm : AEStronglyMeasurable (fun x : ℝ => cosineIntegral (a * |x|)) volume :=
      (hCmeas.comp (measurable_const.mul measurable_id.abs)).aestronglyMeasurable
    have hi := (CosineIntegralGram.result a a ha ha).1
    have hmem := (memLp_two_iff_integrable_sq hm).2 (by simpa [pow_two] using hi)
    exact (hmem.const_mul 2).ofReal
  have hmdata (a : ℝ) (ha : 0 < a) : MemLp (m a) 2 volume ∧
      (∫ x : ℝ, ‖m a x‖ ^ 2) = 4 * Real.pi / a := by
    let b := a / (2 * Real.pi)
    have hb : 0 < b := div_pos ha (by positivity)
    let r : ℝ → ℝ := (Ici b).indicator (fun x : ℝ => x ^ (-2 : ℝ))
    have hr : Integrable r := by
      apply (integrable_indicator_iff measurableSet_Ici).2
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_Ioi_rpow_of_lt (by norm_num) hb
    have hrn : Integrable (fun x : ℝ => r (-x)) := by
      simpa using hr.comp_neg
    have heq : (fun x : ℝ => ‖m a x‖ ^ 2) = fun x => r x + r (-x) := by
      funext x
      dsimp [m, r, b]
      by_cases hx : 0 ≤ x
      · rw [abs_of_nonneg hx]
        have hneg : ¬a / (2 * Real.pi) ≤ -x := by dsimp [b] at hb; linarith
        simp only [indicator_apply, mem_Ici, if_neg hneg, add_zero]
        by_cases h : a / (2 * Real.pi) ≤ x
        · simp only [if_pos h, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
          rw [Real.rpow_neg (hb.le.trans h), Real.rpow_two]
          norm_num
        · simp [h]
      · have hneg : x < 0 := lt_of_not_ge hx
        rw [abs_of_neg hneg]
        have hnot : ¬a / (2 * Real.pi) ≤ x := by dsimp [b] at hb; linarith
        simp only [indicator_apply, mem_Ici, if_neg hnot, zero_add]
        by_cases h : a / (2 * Real.pi) ≤ -x
        · simp only [if_pos h, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
          rw [Real.rpow_neg (hb.le.trans h), Real.rpow_two]
          norm_num
        · simp [h]
    constructor
    · apply (memLp_two_iff_integrable_sq_norm (by
        apply Measurable.aestronglyMeasurable
        exact Complex.measurable_ofReal.comp (Measurable.ite
          (measurableSet_le measurable_const measurable_id.abs)
          (measurable_const.div measurable_id.abs) measurable_const))).2
      rw [heq]
      exact hr.add hrn
    · rw [heq, integral_add hr hrn, integral_neg_eq_self]
      have hi : (∫ x : ℝ, r x) = 1 / b := by
        dsimp [r]
        rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
          integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hb]
        norm_num [Real.rpow_neg_one]
      rw [hi]
      dsimp [b]
      field_simp
      ring
  have hm (a : ℝ) (ha : 0 < a) : MemLp (m a) 2 volume := (hmdata a ha).1
  have hqmass (a : ℝ) (ha : 0 < a) : (∫ x : ℝ, ‖q a x‖ ^ 2) = 4 * Real.pi / a := by
    have heq : (fun x : ℝ => ‖q a x‖ ^ 2) =
        fun x => 4 * (cosineIntegral (a * |x|) * cosineIntegral (a * |x|)) := by
      funext x
      dsimp [q]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    rw [heq, integral_const_mul, (CosineIntegralGram.result a a ha ha).2, max_self]
    ring
  -- The fundamental theorem of calculus identifies finite cosine bands with tail differences.
  have hCidiff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ t in a..b, Real.cos t / t) = cosineIntegral b - cosineIntegral a := by
    have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := by
      rcases mem_uIcc.mp ht with h | h <;> linarith [h.1]
    have hcint : IntervalIntegrable (fun t : ℝ => Real.cos t / t) volume a b := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      exact (Real.continuous_cos.continuousAt.div continuousAt_id
        (hpos t ht).ne').continuousWithinAt
    have hsint : IntervalIntegrable (fun t : ℝ => Real.sin t / t ^ 2) volume a b := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      exact (Real.continuous_sin.continuousAt.div (continuousAt_id.pow 2)
        (pow_ne_zero 2 (hpos t ht).ne')).continuousWithinAt
    have htail (d : ℝ) (hd : 0 < d) :
        IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi d) := by
      refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hd).mono' ?_ ?_
      · exact (Real.measurable_sin.div (measurable_id.pow_const 2)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := hd.trans ht
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos ht0,
          Real.rpow_neg ht0.le, Real.rpow_two]
        simpa [one_div] using div_le_div_of_nonneg_right (Real.abs_sin_le_one t) (sq_nonneg t)
    have hd (t : ℝ) (ht : t ∈ uIcc a b) :
        HasDerivAt (fun u : ℝ => Real.sin u / u)
          (Real.cos t / t - Real.sin t / t ^ 2) t := by
      apply ((Real.hasDerivAt_sin t).div (hasDerivAt_id t) (hpos t ht).ne').congr_deriv
      simp only [id_eq]
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcint.sub hsint)
    rw [intervalIntegral.integral_sub hcint hsint] at hi
    have ht := intervalIntegral.integral_Ioi_sub_Ioi' (htail a ha) (htail b hb)
    dsimp [cosineIntegral]
    linarith
  have hCscale (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
      (∫ t in a..b, Real.cos (k * t) / t) =
        cosineIntegral (k * b) - cosineIntegral (k * a) := by
    have he : (fun t : ℝ => Real.cos (k*t) / t) =
        fun t => k * (Real.cos (k*t) / (k*t)) := by
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · field_simp
    rw [he, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t : ℝ => Real.cos t / t) hk.ne']
    simp only [smul_eq_mul, mul_inv_cancel_left₀ hk.ne']
    exact hCidiff (k*a) (k*b) (mul_pos hk ha) (mul_pos hk hb)
  have hband (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      let u : ℝ → ℂ := (Icc a b).indicator (fun t => (-1 : ℂ) / (t : ℂ))
      let p : ℝ → ℂ := fun t => u t + u (-t)
      Integrable p ∧ ∀ x : ℝ, x ≠ 0 →
        𝓕⁻ p x = q (2 * Real.pi * a) x - q (2 * Real.pi * b) x := by
    let u : ℝ → ℂ := (Icc a b).indicator (fun t => (-1 : ℂ) / (t : ℂ))
    have hu : Integrable u := by
      apply (integrable_indicator_iff measurableSet_Icc).2
      apply ContinuousOn.integrableOn_Icc
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact continuousAt_const.div Complex.continuous_ofReal.continuousAt
        (Complex.ofReal_ne_zero.mpr (ha.trans_le ht.1).ne')
    refine ⟨hu.add hu.comp_neg, ?_⟩
    intro x hx
    have hU (y : ℝ) : 𝓕⁻ u y =
        ∫ t in a..b, Complex.exp ((2 * Real.pi * (t*y) : ℝ) * Complex.I) *
          ((-1 : ℂ) / (t : ℂ)) := by
      rw [Real.fourierInv_eq']
      change (∫ t : ℝ, Complex.exp ((2 * Real.pi * (y*t) : ℝ) * Complex.I) * u t) = _
      calc
        _ = ∫ t : ℝ, (Icc a b).indicator
            (fun t => Complex.exp ((2 * Real.pi * (t*y) : ℝ) * Complex.I) *
              ((-1 : ℂ) / (t : ℂ))) t := by
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ Icc a b <;> simp [u, ht, mul_comm y t]
        _ = _ := by
          rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hab]
    have huint (y : ℝ) : IntervalIntegrable
        (fun t : ℝ => Complex.exp ((2 * Real.pi * (t*y) : ℝ) * Complex.I) *
          ((-1 : ℂ) / (t : ℂ))) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      intro t ht
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul
      · fun_prop
      · exact continuousAt_const.div Complex.continuous_ofReal.continuousAt
          (Complex.ofReal_ne_zero.mpr (ha.trans_le ht.1).ne')
    have hadd : 𝓕⁻ (fun t => u t + u (-t)) x = 𝓕⁻ u x + 𝓕⁻ u (-x) := by
      have hh := congrFun (VectorFourier.fourierIntegral_add
        (e := Real.fourierChar) (L := -innerₗ ℝ) Real.continuous_fourierChar
        (show Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2) by fun_prop)
        hu hu.comp_neg) x
      change 𝓕⁻ (fun t => u t + u (-t)) x =
        𝓕⁻ u x + 𝓕⁻ (fun t => u (-t)) x at hh
      rw [show 𝓕⁻ (fun t => u (-t)) x = 𝓕⁻ u (-x) from
        Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) u x] at hh
      exact hh
    change 𝓕⁻ (fun t => u t + u (-t)) x = _
    rw [hadd, hU, hU, ← intervalIntegral.integral_add (huint x) (huint (-x))]
    have he (t : ℝ) :
        Complex.exp ((2 * Real.pi * (t*x) : ℝ) * Complex.I) * ((-1 : ℂ) / (t : ℂ)) +
        Complex.exp ((2 * Real.pi * (t*(-x)) : ℝ) * Complex.I) * ((-1 : ℂ) / (t : ℂ)) =
          (-2 * (Real.cos ((2 * Real.pi * |x|) * t) / t) : ℝ) := by
      rw [← add_mul]
      have heq : (↑(2 * Real.pi * (t * -x)) : ℂ) = -(↑(2 * Real.pi * (t*x)) : ℂ) := by push_cast; ring
      rw [heq, ← Complex.two_cos, ← Complex.ofReal_cos]
      have hc : Real.cos (2 * Real.pi * (t*x)) = Real.cos ((2*Real.pi*|x|)*t) := by
        by_cases hxp : 0 ≤ x
        · rw [abs_of_nonneg hxp]; congr 1; ring
        · rw [abs_of_neg (lt_of_not_ge hxp)]
          convert (Real.cos_neg (2*Real.pi*(t*x))).symm using 1 <;> congr 1 <;> ring
      rw [hc]
      push_cast
      ring
    simp_rw [he]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
      hCscale a b (2*Real.pi*|x|) ha (ha.trans_le hab) (by positivity)]
    dsimp [q]
    push_cast
    simp only [mul_left_comm, mul_comm]
    ring
  -- Duality and injectivity of the distribution embedding identify the L2 transform.
  have hcompat (f g : ℝ → ℂ) (hf : Integrable f) (hf2 : MemLp f 2 volume)
      (hg2 : MemLp g 2 volume) (he : 𝓕⁻ f =ᵐ[volume] g) :
      𝓕⁻ (hf2.toLp f) = hg2.toLp g := by
    have hinj : Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2) :=
      LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
    apply hinj
    change Lp.toTemperedDistribution (𝓕⁻ (hf2.toLp f)) =
      Lp.toTemperedDistribution (hg2.toLp g)
    rw [← Lp.fourierInv_toTemperedDistribution_eq]
    ext φ
    simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul]
    calc
      _ = ∫ x : ℝ, (𝓕⁻ φ) x * f x := by
        apply integral_congr_ae
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx]
      _ = ∫ x : ℝ, φ x * 𝓕⁻ f x := by
        have hflip : (-innerₗ ℝ).flip = -innerₗ ℝ := by
          ext
          simp
        have hi := VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := -innerₗ ℝ) (μ := volume) (ν := volume) Real.continuous_fourierChar
          (show Continuous (fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2) by fun_prop)
          φ.integrable hf
        rw [hflip] at hi
        change (∫ x : ℝ, 𝓕⁻ (fun t => φ t) x * f x) =
          ∫ x : ℝ, φ x * 𝓕⁻ f x at hi
        simpa only [SchwartzMap.fourierInv_coe] using hi
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [he, hg2.coeFn_toLp] with x hx hgx
        rw [hx, hgx]
  have hbandLp (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
      𝓕⁻ ((hm (2*Real.pi*a) (by positivity)).toLp (m (2*Real.pi*a)) -
        (hm (2*Real.pi*b) (mul_pos (by positivity) (ha.trans_le hab))).toLp (m (2*Real.pi*b))) =
      (hq (2*Real.pi*a) (by positivity)).toLp (q (2*Real.pi*a)) -
        (hq (2*Real.pi*b) (mul_pos (by positivity) (ha.trans_le hab))).toLp (q (2*Real.pi*b)) := by
    have hb : 0 < b := ha.trans_le hab
    let u : ℝ → ℂ := (Icc a b).indicator (fun t => (-1 : ℂ) / (t : ℂ))
    let p : ℝ → ℂ := fun t => u t + u (-t)
    have hband' := hband a b ha hab
    have hp : Integrable p := hband'.1
    have he : p =ᵐ[volume] fun x => m (2*Real.pi*a) x - m (2*Real.pi*b) x := by
      filter_upwards [volume.ae_ne b, volume.ae_ne (-b)] with x hxb hxnb
      have hcancel (d : ℝ) : 2 * Real.pi * d / (2 * Real.pi) = d := by
        field_simp
      have ht : 0 ≤ |x| := abs_nonneg x
      have htb : |x| ≠ b := by
        intro h
        rcases (abs_eq (by positivity : 0 ≤ b)).mp h with h | h
        · exact hxb h
        · exact hxnb h
      have hev : p x = p |x| := by
        by_cases hx : 0 ≤ x
        · rw [abs_of_nonneg hx]
        · rw [abs_of_neg (lt_of_not_ge hx)]
          simp [p, add_comm]
      rw [hev]
      have hneg : ¬a ≤ -|x| := by linarith
      dsimp [p, u, m]
      simp only [hcancel, indicator_apply, mem_Icc, not_and_of_not_left _ hneg, if_false,
        add_zero]
      by_cases hax : a ≤ |x|
      · by_cases hbx : b ≤ |x|
        · have hnot : ¬ |x| ≤ b := by intro h; exact htb (le_antisymm h hbx)
          simp [hax, hbx, hnot]
        · have hle : |x| ≤ b := le_of_not_ge hbx
          simp [hax, hbx, hle]
      · have hbx : ¬ b ≤ |x| := by intro h; exact hax (hab.trans h)
        simp [hax, hbx]
    have hf2 : MemLp (fun x => m (2*Real.pi*a) x - m (2*Real.pi*b) x) 2 volume :=
      (hm _ (by positivity)).sub (hm _ (by positivity))
    have hg2 : MemLp (fun x => q (2*Real.pi*a) x - q (2*Real.pi*b) x) 2 volume :=
      (hq _ (by positivity)).sub (hq _ (by positivity))
    have hi := hcompat _ _ (hp.congr he) hf2 hg2 (by
      have hi : 𝓕⁻ p =ᵐ[volume] fun x => q (2*Real.pi*a) x - q (2*Real.pi*b) x := by
        filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
        exact hband'.2 x hx
      filter_upwards [hi] with x hx
      rw [← Real.fourierInv_congr_ae he]
      exact hx)
    change 𝓕⁻ (hf2.toLp (m (2*Real.pi*a) - m (2*Real.pi*b))) =
      hg2.toLp (q (2*Real.pi*a) - q (2*Real.pi*b)) at hi
    rw [(hm _ (by positivity)).toLp_sub (hm _ (by positivity)),
      (hq _ (by positivity)).toLp_sub (hq _ (by positivity))] at hi
    exact hi
  refine ⟨hq c hc, hm c hc, ?_⟩
  have hnorm (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
      ‖hf.toLp f‖ = Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    rw [Lp.norm_toLp, toReal_eLpNorm hf.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow]
  -- Both omitted tails have squared L2 norm 4 pi/R and tend to zero.
  let R : ℕ → ℝ := fun n => c + (n : ℝ) + 1
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  have hRc (n : ℕ) : c ≤ R n := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have htop : Tendsto R atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [R]; linarith [hc]) tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n => Real.sqrt (4 * Real.pi / R n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop htop :
      Tendsto (fun n => 4 * Real.pi / R n) atTop (𝓝 0)).sqrt
  let Q (a : ℝ) (ha : 0 < a) := (hq a ha).toLp (q a)
  let M (a : ℝ) (ha : 0 < a) := (hm a ha).toLp (m a)
  have hQ0 : Tendsto (fun n => Q (R n) (hR n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact hlim.congr fun n => (show ‖Q (R n) (hR n)‖ = _ by
      dsimp only [Q]
      rw [hnorm, hqmass _ (hR n)]).symm
  have hM0 : Tendsto (fun n => M (R n) (hR n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact hlim.congr fun n => (show ‖M (R n) (hR n)‖ = _ by
      dsimp only [M]
      rw [hnorm, (hmdata _ (hR n)).2]).symm
  have hseq (n : ℕ) : 𝓕⁻ (M c hc - M (R n) (hR n)) =
      Q c hc - Q (R n) (hR n) := by
    have hh := hbandLp (c/(2*Real.pi)) (R n/(2*Real.pi))
      (by positivity) ((div_le_div_iff_of_pos_right (by positivity)).mpr (hRc n))
    have he (a : ℝ) : 2 * Real.pi * (a / (2*Real.pi)) = a := by field_simp
    simpa only [he, M, Q] using hh
  have htL : Tendsto (fun n => 𝓕⁻ (M c hc - M (R n) (hR n))) atTop
      (𝓝 (𝓕⁻ (M c hc))) := by
    have hh := ((Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous.tendsto (M c hc)).comp
      (show Tendsto (fun n => M c hc - M (R n) (hR n)) atTop (𝓝 (M c hc)) by
        simpa using tendsto_const_nhds.sub hM0)
    exact hh
  have htR : Tendsto (fun n => Q c hc - Q (R n) (hR n)) atTop (𝓝 (Q c hc)) := by
    simpa using tendsto_const_nhds.sub hQ0
  have heq : 𝓕⁻ (M c hc) = Q c hc :=
    tendsto_nhds_unique htL (htR.congr (fun n => (hseq n).symm))
  have heq' := congrArg (Lp.fourierTransformₗᵢ ℝ ℂ) heq
  exact heq'.symm.trans ((Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply (M c hc))

end D5.S3.Fourier.Asymptotics.CosineIntegralMultiplier

#print axioms D5.S3.Fourier.Asymptotics.CosineIntegralMultiplier.result
