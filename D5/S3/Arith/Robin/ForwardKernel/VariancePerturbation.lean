/- GID: D5/S3/Arith/Robin/ForwardKernel/VariancePerturbation
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/VariancePerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negligible variance perturbations preserve uniform common-band asymptotics. -/

import D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpnessDefs
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransfer
import D5.S3.Arith.Robin.ForwardKernel.DyadicSmoothingBounds

/-! Abstract stability under locally bounded measurable perturbations. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open VarianceTransferDefs VarianceTransfer
open scoped Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine variance error is controlled by the two original variances.
Consumed by `band_asymptotic_affine` in `CommonBandSharpness`. -/
theorem cumulativeVariance_affine_error
    {E F : ℝ → ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hF : LocallyBoundedMeasurable F)
    {Y : ℝ} (hY : 1 ≤ Y) (u t : ℝ) :
    |cumulativeVariance (fun x => E x + t * F x) Y u -
        cumulativeVariance E Y u| ≤
      2 * |t| *
          Real.sqrt
            (cumulativeVariance E Y u *
              cumulativeVariance F Y u) +
        t ^ 2 * cumulativeVariance F Y u := by
  have he := DyadicSmoothingBounds.lbm_memLp
    (DyadicSmoothingBounds.increment_lbm hE u) 1 Y
  have hf := DyadicSmoothingBounds.lbm_memLp
    (DyadicSmoothingBounds.increment_lbm hF u) 1 Y
  have ha : MemLp (increment (fun x => E x + t * F x) u) 2
      (volume.restrict (Ioc 1 Y)) := by
    convert he.add (hf.const_smul t) using 1
    ext x
    simp only [increment, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hdiff : (fun x => increment (fun x => E x + t * F x) u x - increment E u x) =
      t • increment F u := by
    ext x
    simp only [increment, Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm : Real.sqrt (∫ x in (1 : ℝ)..Y,
        (increment (fun x => E x + t * F x) u x - increment E u x) ^ 2) =
      |t| * Real.sqrt (cumulativeVariance F Y u) := by
    change CrossExponentDefs.intervalL2 1 Y _ = _
    rw [← lpNorm_two_eq_intervalL2 hY (f := fun x =>
        increment (fun x => E x + t * F x) u x - increment E u x)
        (ha.sub he).aestronglyMeasurable,
      hdiff, lpNorm_const_smul,
      lpNorm_two_eq_intervalL2 hY hf.aestronglyMeasurable]
    rfl
  have hr := interval_l2_reverse_triangle hY ha he
  rw [hnorm] at hr
  change |Real.sqrt (cumulativeVariance (fun x => E x + t * F x) Y u) -
    Real.sqrt (cumulativeVariance E Y u)| ≤ |t| * Real.sqrt (cumulativeVariance F Y u) at hr
  have hn (G : ℝ → ℝ) : 0 ≤ cumulativeVariance G Y u :=
    intervalIntegral.integral_nonneg_of_forall hY fun _ => sq_nonneg _
  have hid : cumulativeVariance (fun x => E x + t * F x) Y u -
        cumulativeVariance E Y u =
      (Real.sqrt (cumulativeVariance (fun x => E x + t * F x) Y u) -
        Real.sqrt (cumulativeVariance E Y u)) *
      (Real.sqrt (cumulativeVariance (fun x => E x + t * F x) Y u) +
        Real.sqrt (cumulativeVariance E Y u)) := by
    nlinarith [Real.sq_sqrt (hn (fun x => E x + t * F x)), Real.sq_sqrt (hn E)]
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  calc
    _ ≤ (|t| * Real.sqrt (cumulativeVariance F Y u)) *
        (2 * Real.sqrt (cumulativeVariance E Y u) +
          |t| * Real.sqrt (cumulativeVariance F Y u)) :=
      mul_le_mul hr (by linarith [(abs_le.mp hr).2]) (by positivity) (by positivity)
    _ = 2 * |t| * Real.sqrt (cumulativeVariance E Y u * cumulativeVariance F Y u) +
        t ^ 2 * cumulativeVariance F Y u := by
      rw [Real.sqrt_mul (hn E)]
      calc
        _ = 2 * |t| * (Real.sqrt (cumulativeVariance E Y u) *
            Real.sqrt (cumulativeVariance F Y u)) +
            |t| ^ 2 * (Real.sqrt (cumulativeVariance F Y u)) ^ 2 := by ring
        _ = _ := by rw [sq_abs, Real.sq_sqrt (hn F)]

/-- A perturbation with uniformly negligible band variance preserves the asymptotic.
Consumed by `CommonBandSharpness.common_band_near_optimality`. -/
theorem band_asymptotic_affine
    {E F : ℝ → ℝ} {α β : ℝ}
    (_hα : 0 < α) (_hαβ : α < β) (hβ : β < 1)
    (hE : LocallyBoundedMeasurable E)
    (hF : LocallyBoundedMeasurable F)
    (hV : CumulativeVarianceBandAsymptoticFor E α β)
    (hN : CumulativeVarianceBandNegligibleFor F α β)
    (t : ℝ) :
    CumulativeVarianceBandAsymptoticFor
      (fun x => E x + t * F x) α β := by
  intro ε hε
  have hc : Tendsto (fun d : ℝ => 2 * |t| * Real.sqrt (2 * d) + t ^ 2 * d)
      (𝓝 0) (𝓝 0) := by
    have hc' : ContinuousAt (fun d : ℝ => 2 * |t| * Real.sqrt (2 * d) + t ^ 2 * d) 0 := by
      fun_prop
    simpa only [mul_zero, Real.sqrt_zero, add_zero] using hc'.tendsto
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (gt_mem_nhds (half_pos hε)))
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδb : 2 * |t| * Real.sqrt (2 * δ) + t ^ 2 * δ < ε / 2 :=
    hrb (show dist δ 0 < r by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ]
      exact half_lt_self hr)
  filter_upwards [hV (min (ε / 2) 1) (lt_min (half_pos hε) zero_lt_one),
    hN δ hδ, eventually_gt_atTop (1 : ℝ)] with Y hv hn hY
  intro u hlu huu
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hu : 0 < u := (Real.rpow_pos_of_pos hY0 α).trans_le hlu
  have huY : u < Y := huu.trans_lt (Real.rpow_lt_self_of_one_lt hY hβ)
  let M := Y * u * Real.log (Y / u)
  have hM : 0 < M := mul_pos (mul_pos hY0 hu)
    (Real.log_pos ((one_lt_div hu).mpr huY))
  have hve := hv u hlu huu
  have hvf := hn u hlu huu
  have hF0 : 0 ≤ cumulativeVariance F Y u :=
    intervalIntegral.integral_nonneg_of_forall hY.le fun _ => sq_nonneg _
  have hEb : cumulativeVariance E Y u ≤ 2 * M := by
    have he := (abs_le.mp hve).2.trans (min_le_right _ _)
    have he' : cumulativeVariance E Y u / M ≤ 2 := by dsimp [M]; linarith
    exact (div_le_iff₀ hM).mp he'
  have hFb : cumulativeVariance F Y u ≤ δ * M := by
    exact (div_le_iff₀ hM).mp ((le_abs_self _).trans hvf)
  have hroot : Real.sqrt (cumulativeVariance E Y u * cumulativeVariance F Y u) ≤
      Real.sqrt (2 * δ) * M := by
    calc
      _ ≤ Real.sqrt ((2 * M) * (δ * M)) :=
        Real.sqrt_le_sqrt (mul_le_mul hEb hFb hF0 (by positivity))
      _ = Real.sqrt ((2 * δ) * M ^ 2) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hM.le]
  have herr := cumulativeVariance_affine_error hE hF hY.le u t
  have herr' :
      |cumulativeVariance (fun x => E x + t * F x) Y u - cumulativeVariance E Y u| / M ≤
        2 * |t| * Real.sqrt (2 * δ) + t ^ 2 * δ := by
    apply (div_le_iff₀ hM).mpr
    calc
      _ ≤ 2 * |t| * (Real.sqrt (2 * δ) * M) + t ^ 2 * (δ * M) :=
        herr.trans (add_le_add (mul_le_mul_of_nonneg_left hroot (by positivity))
          (mul_le_mul_of_nonneg_left hFb (sq_nonneg t)))
      _ = _ := by ring
  calc
    _ = |(cumulativeVariance (fun x => E x + t * F x) Y u -
          cumulativeVariance E Y u) / M + (cumulativeVariance E Y u / M - 1)| := by
      congr 1
      dsimp [M]
      ring
    _ ≤ |(cumulativeVariance (fun x => E x + t * F x) Y u -
          cumulativeVariance E Y u) / M| + |cumulativeVariance E Y u / M - 1| :=
      abs_add_le _ _
    _ ≤ (2 * |t| * Real.sqrt (2 * δ) + t ^ 2 * δ) + min (ε / 2) 1 := by
      rw [abs_div, abs_of_pos hM]
      exact add_le_add herr' hve
    _ ≤ ε := by linarith [min_le_left (ε / 2) 1]

end

end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
