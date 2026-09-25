/- GID: D5/S3/Fourier/Asymptotics/CosineIntegralGram
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/CosineIntegralGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive dilations of the real cosine-integral tail have an absolutely integrable product with integral pi divided by the larger scale. -/

import D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
import D5.S3.TotalVariation.Asymptotics.StatLeanFourierCore
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set Filter
open scoped Topology
open D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)

namespace D5.S3.Fourier.Asymptotics.CosineIntegralGram

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Absolute integrability and the exact Gram integral of the real cosine-integral tails. -/
theorem result : ∀ a b : ℝ, 0 < a → 0 < b →
    Integrable (fun z : ℝ => cosineIntegral (a * |z|) * cosineIntegral (b * |z|)) ∧
    (∫ z : ℝ, cosineIntegral (a * |z|) * cosineIntegral (b * |z|)) = Real.pi / max a b := by
  -- The absolutely convergent sine tail supplies the derivative on the positive half-line.
  let f : ℝ → ℝ := fun t => Real.sin t / t ^ 2
  let T : ℝ → ℝ := fun x => cosineIntegral x - Real.sinc x
  have hmajor (x : ℝ) (hx : 0 < x) : ‖f x‖ ≤ x ^ (-2 : ℝ) := by
    dsimp [f]
    rw [abs_div, abs_pow, abs_of_pos hx,
      Real.rpow_neg hx.le, Real.rpow_two]
    simpa [one_div] using div_le_div_of_nonneg_right (Real.abs_sin_le_one x) (sq_nonneg x)
  have htailint (x : ℝ) (hx : 0 < x) : IntegrableOn f (Ioi x) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx).mono' ?_ ?_
    · exact (Real.measurable_sin.div (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hmajor t (hx.trans ht)
  have hT (x : ℝ) (hx : 0 < x) : T x = -(∫ t in Ioi x, f t) := by
    simp [T, cosineIntegral, Real.sinc_of_ne_zero hx.ne', f]
  have hfcont : ContinuousOn f (Ioi 0) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    dsimp [f]
    exact Real.continuous_sin.continuousAt.div
      (continuousAt_id.pow 2) (pow_ne_zero 2 (ne_of_gt hx))
  have hTderiv (x : ℝ) (hx : 0 < x) : HasDerivAt T (Real.sinc x / x) x := by
    have hi : IntervalIntegrable f volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      exact hfcont.mono (by
        intro y hy
        rcases Set.mem_uIcc.mp hy with h | h <;> simp only [mem_Ioi] <;> linarith [h.1, h.2])
    have hd := intervalIntegral.integral_hasDerivAt_right hi
      ((Real.measurable_sin.div (measurable_id.pow_const 2)).stronglyMeasurable.stronglyMeasurableAtFilter)
      ((hfcont x hx).continuousAt (Ioi_mem_nhds hx))
    have he : T =ᶠ[𝓝 x] fun y => -(∫ t in Ioi (1 : ℝ), f t) + ∫ t in (1 : ℝ)..y, f t := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [hT y hy, ← intervalIntegral.integral_Ioi_sub_Ioi' (htailint 1 zero_lt_one) (htailint y hy)]
      ring
    have hd' := hd.const_add (-(∫ t in Ioi (1 : ℝ), f t))
    apply (hd'.congr_of_eventuallyEq he).congr_deriv
    simp [f, Real.sinc_of_ne_zero hx.ne', pow_two, div_div]
  have hBderiv (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
      HasDerivAt (fun y => y * T (a * y) * T (b * y))
        (cosineIntegral (a * x) * cosineIntegral (b * x) - Real.sinc (a * x) * Real.sinc (b * x)) x := by
    have hdA := (hTderiv (a*x) (mul_pos ha hx)).comp x ((hasDerivAt_id x).const_mul a)
    have hdB := (hTderiv (b*x) (mul_pos hb hx)).comp x ((hasDerivAt_id x).const_mul b)
    apply (((hasDerivAt_id x).mul hdA).mul hdB).congr_deriv
    dsimp [T]
    field_simp
    ring
  -- Both boundary terms vanish; the small-argument estimate comes from N = 1.
  have hTlarge (x : ℝ) (hx : 0 < x) : |T x| ≤ 1 / x := by
    rw [hT x hx, abs_neg]
    have h := (norm_integral_le_integral_norm f (μ := volume.restrict (Ioi x))).trans
      (integral_mono_ae (htailint x hx).norm
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx) (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hmajor t (hx.trans ht)))
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hx] at h
    norm_num [Real.rpow_neg_one, Real.norm_eq_abs, one_div] at h ⊢
    exact h
  obtain ⟨K, hK, hrem⟩ := D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result
  have hTsmall (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : |T x| ≤ 2 + 2*K + |Real.log x| := by
    have hr := hrem x hx hx1 1 (by norm_num)
    have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    norm_num [Finset.sum_Icc_succ_top, max_eq_left hl] at hr
    have hr' : |Real.cos x - (-Real.log x + cosineIntegral x)| ≤ 2*K := by
      apply hr.trans
      nlinarith
    have hc : |cosineIntegral x| ≤ 1 + 2*K + |Real.log x| := by
      have h1 := (abs_le.mp hr').1
      have h2 := (abs_le.mp hr').2
      rw [abs_le]
      constructor <;> nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x,
        le_abs_self (Real.log x), neg_abs_le (Real.log x)]
    change |cosineIntegral x - Real.sinc x| ≤ _
    exact (abs_sub _ _).trans (by linarith [Real.abs_sinc_le_one x])
  have hrootT : Tendsto (fun x : ℝ => Real.sqrt x * T x) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have hl := (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0:ℝ) < 1/2)).abs
    have hm : Tendsto (fun x : ℝ => Real.sqrt x * (2 + 2*K + |Real.log x|)) (𝓝[>] 0) (𝓝 0) := by
      have hh := (hs.mul_const (2+2*K)).add hl
      convert hh using 1
      · funext x
        rw [abs_mul, ← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg x)]
        ring
      · simp
    apply squeeze_zero_norm' _ hm
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg x)]
    exact mul_le_mul_of_nonneg_left (hTsmall x hx.1 hx.2) (Real.sqrt_nonneg x)
  have hBzero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Tendsto (fun x : ℝ => x*T (a*x)*T (b*x)) (𝓝[>] 0) (𝓝 0) := by
    have hscale (c : ℝ) (hc : 0 < c) : Tendsto (fun x : ℝ => c*x) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨by simpa using (tendsto_const_nhds.mul tendsto_id : Tendsto (fun x : ℝ => c*x) (𝓝 0) (𝓝 (c*0))).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos hc hx
    have hh := ((hrootT.comp (hscale a ha)).mul (hrootT.comp (hscale b hb))).div_const (Real.sqrt a * Real.sqrt b)
    simp only [zero_mul, zero_div] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    dsimp [Function.comp_def]
    rw [Real.sqrt_mul ha.le, Real.sqrt_mul hb.le]
    have hx2 := Real.sq_sqrt (le_of_lt (show 0 < x from hx))
    field_simp
    ring_nf
    rw [hx2]
  have hBtop (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Tendsto (fun x : ℝ => x*T (a*x)*T (b*x)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => (1/(a*b))*x⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (1/(a*b))
    apply squeeze_zero_norm' _ hh
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx]
    calc
      x * |T (a*x)| * |T (b*x)| ≤ x * (1/(a*x)) * (1/(b*x)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hTlarge _ (mul_pos ha hx)) hx.le)
          (hTlarge _ (mul_pos hb hx)) (abs_nonneg _) (by positivity)
      _ = (1/(a*b))*x⁻¹ := by field_simp
  -- Normalize the sinc pairing by the existing squared-sine integral.
  have hq (c : ℝ) : Integrable (fun x : ℝ => (Real.sin (c*x)/x)^2) ∧
      (∫ x : ℝ, (Real.sin (c*x)/x)^2) = Real.pi * |c| := by
    by_cases hc : c = 0
    · subst c
      simp
    have he : (fun x : ℝ => (Real.sin (c*x)/x)^2) =
        fun x => c^2 * (Real.sin (c*x)/(c*x))^2 := by
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · field_simp
    rw [he]
    refine ⟨(StatLean.HypothesisTesting.integrable_sin_div_sq.comp_mul_left' hc).const_mul _, ?_⟩
    rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ => (Real.sin x/x)^2) c,
      StatLean.HypothesisTesting.integral_sin_div_sq, smul_eq_mul, abs_inv]
    have hca : |c| ≠ 0 := abs_ne_zero.mpr hc
    field_simp
    nlinarith [sq_abs c]
  have hSsq (a : ℝ) (ha : 0 < a) : Integrable (fun x : ℝ => Real.sinc (a*x)^2) := by
    have hi := StatLean.HypothesisTesting.integrable_sin_div_sq.comp_mul_left' ha.ne'
    apply hi.congr
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with x hx
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha.ne' (by simpa using hx))]
  have hSint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Integrable (fun x : ℝ => Real.sinc (a*x)*Real.sinc (b*x)) :=
    ((memLp_two_iff_integrable_sq (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr (hSsq a ha)).integrable_mul
      ((memLp_two_iff_integrable_sq (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr (hSsq b hb))
  have hSmass (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ x : ℝ, Real.sinc (a*x)*Real.sinc (b*x)) = Real.pi / max a b := by
    let p := (a+b)/2
    let q := (a-b)/2
    have he : (fun x : ℝ => Real.sinc (a*x)*Real.sinc (b*x)) =ᵐ[volume]
        fun x => ((Real.sin (p*x)/x)^2 - (Real.sin (q*x)/x)^2)/(a*b) := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      rw [Real.sinc_of_ne_zero (mul_ne_zero ha.ne' hx0),
        Real.sinc_of_ne_zero (mul_ne_zero hb.ne' hx0)]
      have hp := Real.cos_two_mul_eq_one_sub (p*x)
      have hq' := Real.cos_two_mul_eq_one_sub (q*x)
      have hsub := Real.cos_sub (a*x) (b*x)
      have hadd := Real.cos_add (a*x) (b*x)
      have hep : 2*(p*x) = a*x+b*x := by dsimp [p]; ring
      have heq : 2*(q*x) = a*x-b*x := by dsimp [q]; ring
      rw [hep, hadd] at hp
      rw [heq, hsub] at hq'
      field_simp
      ring_nf at hp hq' ⊢
      nlinarith
    rw [integral_congr_ae he, integral_div,
      integral_sub (hq p).1 (hq q).1, (hq p).2, (hq q).2]
    have hp : 0 < p := by dsimp [p]; positivity
    rw [abs_of_pos hp]
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab, abs_of_nonpos (show q ≤ 0 by dsimp [q]; linarith)]
      dsimp [p,q]
      field_simp
      ring
    · rw [max_eq_left hba, abs_of_nonneg (show 0 ≤ q by dsimp [q]; linarith)]
      dsimp [p,q]
      field_simp
      ring
  have hScont (a b : ℝ) : Continuous (fun x : ℝ => Real.sinc (a*x)*Real.sinc (b*x)) :=
    (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
  -- The nonnegative diagonal derivative establishes integrability before mixed FTC.
  let P : ℝ → ℝ → ℝ → ℝ := fun a b x =>
    x*T (a*x)*T (b*x) + ∫ t in (0:ℝ)..x, Real.sinc (a*t)*Real.sinc (b*t)
  have hPzero (a b : ℝ) : P a b 0 = 0 := by simp [P]
  have hPcont (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ContinuousWithinAt (P a b) (Ici 0) 0 := by
    rw [← Ioi_insert]
    apply ContinuousWithinAt.insert
    change Tendsto (P a b) (𝓝[>] 0) (𝓝 (P a b 0))
    have hh := (hBzero a b ha hb).add
      (((intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ)) (hScont a b)).continuous.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    simpa [P] using hh
  have hPderiv (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
      HasDerivAt (P a b) (cosineIntegral (a*x)*cosineIntegral (b*x)) x := by
    have hd := intervalIntegral.integral_hasDerivAt_right ((hScont a b).intervalIntegrable 0 x)
      (hScont a b).aestronglyMeasurable.stronglyMeasurableAtFilter (hScont a b).continuousAt
    convert! (hBderiv a b x ha hb hx).add hd using 1
    simp
  have hPtop (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      Tendsto (P a b) atTop (𝓝 (∫ x in Ioi (0:ℝ), Real.sinc (a*x)*Real.sinc (b*x))) := by
    have hh := (hBtop a b ha hb).add
      (intervalIntegral_tendsto_integral_Ioi 0 (hSint a b ha hb).integrableOn tendsto_id)
    simpa [P] using hh
  have hCdiag (a : ℝ) (ha : 0 < a) : IntegrableOn (fun x : ℝ => cosineIntegral (a*x)^2) (Ioi 0) := by
    have hh := integrableOn_Ioi_deriv_of_nonneg (hPcont a a ha ha)
      (fun x hx => hPderiv a a x ha ha hx) (fun x _ => mul_self_nonneg _) (hPtop a a ha ha)
    simpa only [pow_two] using hh
  have hCcont (a : ℝ) (ha : 0 < a) : ContinuousOn (fun x : ℝ => cosineIntegral (a*x)) (Ioi 0) := by
    intro x hx
    have hc : ContinuousAt (fun y : ℝ => a*y) x := continuousAt_const.mul continuousAt_id
    have ht := ((hTderiv (a*x) (mul_pos ha hx)).continuousAt.comp hc).add
      (Real.continuous_sinc.continuousAt.comp hc)
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun y => (cosineIntegral (a*y) - Real.sinc (a*y)) + Real.sinc (a*y)) x at ht
    simpa only [sub_add_cancel] using ht
  have hCint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      IntegrableOn (fun x : ℝ => cosineIntegral (a*x)*cosineIntegral (b*x)) (Ioi 0) :=
    ((memLp_two_iff_integrable_sq ((hCcont a ha).aestronglyMeasurable measurableSet_Ioi)).mpr (hCdiag a ha)).integrable_mul
      ((memLp_two_iff_integrable_sq ((hCcont b hb).aestronglyMeasurable measurableSet_Ioi)).mpr (hCdiag b hb))
  have hCmass (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      (∫ x in Ioi (0:ℝ), cosineIntegral (a*x)*cosineIntegral (b*x)) =
        ∫ x in Ioi (0:ℝ), Real.sinc (a*x)*Real.sinc (b*x) := by
    have hh := integral_Ioi_of_hasDerivAt_of_tendsto (hPcont a b ha hb)
      (fun x hx => hPderiv a b x ha hb hx) (hCint a b ha hb) (hPtop a b ha hb)
    simpa only [hPzero, sub_zero] using hh
  intro a b ha hb
  have hi : IntegrableOn (fun x : ℝ => cosineIntegral (a*|x|)*cosineIntegral (b*|x|)) (Ioi 0) := by
    apply (hCint a b ha hb).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [abs_of_pos (show 0 < x from hx)]
  have hineg : IntegrableOn (fun x : ℝ => cosineIntegral (a*|x|)*cosineIntegral (b*|x|)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  refine ⟨?_, ?_⟩
  · have hh := hineg.union hi
    simpa only [Iic_union_Ioi, integrableOn_univ] using hh
  · rw [integral_comp_abs (f := fun x => cosineIntegral (a*x)*cosineIntegral (b*x)), hCmass a b ha hb]
    have he : (fun x : ℝ => Real.sinc (a*|x|)*Real.sinc (b*|x|)) =
        (fun x : ℝ => Real.sinc (a*x)*Real.sinc (b*x)) := by
      funext x
      rcases le_total 0 x with hx | hx
      · simp [abs_of_nonneg hx]
      · simp [abs_of_nonpos hx, mul_neg, Real.sinc_neg]
    rw [← integral_comp_abs (f := fun x => Real.sinc (a*x)*Real.sinc (b*x)), he, hSmass a b ha hb]

end D5.S3.Fourier.Asymptotics.CosineIntegralGram
