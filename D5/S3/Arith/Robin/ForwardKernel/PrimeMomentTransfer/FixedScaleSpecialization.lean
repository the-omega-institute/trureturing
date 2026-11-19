/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FixedScaleSpecialization
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FixedScaleSpecialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mean-square prime correlations: Logarithmic weights identify fixed-scale Chebyshev moments and variance factors. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.RealLengthTransfer
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.CutoffWeights
import D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentTransferDefs

/-! Exact changes of weight, increment and variance for fixed power lengths. -/

open Set Filter MeasureTheory
open scoped Topology BigOperators
open D5.S3.Arith.Robin.ForwardKernel.FourthTransfer.FourthMomentTransferDefs

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

private theorem p_log_block_mass (u v : ℝ) (_hu : 1 ≤ u) (_huv : u ≤ v) (_hv : v ≤ 2) :
    (∫ t in (1:ℝ)..2, (Icc u v).indicator (fun t : ℝ => 1/(t*Real.log 2)) t) =
      (DyadicProbability.dyadicProbabilityMeasure 1).real (Icc u v) := by
  have hi := DyadicProbability.dyadicProbabilityMeasure_integral
    (by norm_num : (0 : ℝ) < 1) ((Icc u v).indicator (fun _ : ℝ => 1))
  rw [integral_indicator measurableSet_Icc, integral_const] at hi
  simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply
    MeasurableSet.univ, univ_inter] at hi
  change (DyadicProbability.dyadicProbabilityMeasure 1).real (Icc u v) = _ at hi
  rw [hi, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t ht
  by_cases h : t ∈ Icc u v <;> simp [h, div_mul_eq_div_div]

private theorem p_fixed_scale_increment (θ c X x : ℝ) :
    fixedScaleB (fun x => Chebyshev.psi x-x) θ c X x = Z (X^θ) 0 c x X := by
  unfold fixedScaleB VarianceTransferDefs.increment Z Delta
  simp only [zero_mul, add_zero, sub_zero]
  congr 1
  ring

private theorem p_block_moment_identity (X θ u v : ℝ) (k : ℕ) (c : Fin k → ℝ)
    (hX : 0 < X) :
    fixedBlockMoment (fun x => Chebyshev.psi x-x) θ k c u v X =
      weightedMoment X (X^θ) (fun _ => 0) c
        ((Icc u v).indicator (fun t : ℝ => 1/(t*Real.log 2))) := by
  unfold fixedBlockMoment
  simp_rw [p_fixed_scale_increment]
  rw [DyadicProbability.dyadicProbabilityMeasure_integral hX]
  unfold weightedMoment
  rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by linarith : X ≤ 2*X)] at hx
  have hx0 : 0 < x := hX.trans_le hx.1
  unfold MomentTransferDefs.dyadicU
  by_cases h : x/X ∈ Icc u v
  · simp only [indicator_of_mem h, one_mul]
    field_simp
  · simp [h]

private theorem p_power_variance (X θ : ℝ) (hX : 1 < X) :
    kappa X (X^θ) = 1-θ := by
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hlog : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  rw [kappa, Real.log_div hX0.ne' (Real.rpow_pos_of_pos hX0 θ).ne',
    Real.log_rpow hX0]
  field_simp

private theorem p_prefix_w4 (c : Fin 4 → ℝ) (hc : ∀ i, 0 ≤ c i) :
    W4 (fun _ => 0) c = MomentTransferDefs.brownianW4 c := by
  have h (i j : Fin 4) : sigma 0 (c i) 0 (c j) = min (c i) (c j) := by
    simp only [sigma, max_self, sub_zero, max_eq_right (le_min (hc i) (hc j))]
  simp only [W4, h, MomentTransferDefs.brownianW4]

private theorem p_power_in_band (α θ β : ℝ) (hαθ : α ≤ θ) (hθβ : θ ≤ β) :
    ∀ᶠ X : ℝ in atTop, X^α ≤ X^θ ∧ X^θ ≤ X^β := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  exact ⟨Real.rpow_le_rpow_of_exponent_le hX hαθ,
    Real.rpow_le_rpow_of_exponent_le hX hθβ⟩

private theorem p_fixed_scale_third_limit :
∀ (β θ M : ℝ), 0 < θ → θ < β → β < 1/3 →
  MeanSquareHL 3 concreteSS β → IntervalCorrelations concreteSS → 0 < M →
  ∀ (c : Fin 3 → ℝ), (∀ i, c i ∈ Icc (0:ℝ) M) →
  ∀ u v : ℝ, 1 ≤ u → u < v → v ≤ 2 →
  Tendsto (fixedBlockMoment (fun x => Chebyshev.psi x-x) θ 3 c u v) atTop (𝓝 (0)) := by
  intro β θ M hθ hθβ hβ hMS hcor hM c hc u v hu huv hv
  have hα : 0 < θ / 2 := half_pos hθ
  have hαβ : θ / 2 < β := by linarith
  have hadm : admissible (max 1 M) (fun _ => 0) c := by
    intro i
    exact ⟨le_rfl, (hc i).1, (hc i).2.trans (le_max_right 1 M)⟩
  let B := 3 / Real.log 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw := log_block_bv u v hu huv.le hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : 0 < ε / (B + 1) := div_pos hε (by positivity)
  have hbudget : B * (ε / (B + 1)) < ε := by
    have heq : (B + 1) * (ε / (B + 1)) = ε := by field_simp
    nlinarith
  filter_upwards [real_third concreteSS (θ / 2) β (max 1 M)
      hα hαβ hβ concreteSS_empty concreteSS_singleton hMS hcor (le_max_left 1 M)
      (ε / (B + 1)) ht,
    p_power_in_band (θ / 2) θ β (by linarith) hθβ.le,
    eventually_ge_atTop (2 : ℝ)] with X hreal hband hX
  have hX0 : 0 < X := by linarith
  rw [Real.dist_eq, sub_zero, p_block_moment_identity X θ u v 3 c hX0]
  exact (hreal (X ^ θ) hband.1 hband.2 B _ hw (fun _ => 0) c hadm).trans_lt hbudget

private theorem p_fixed_scale_fourth_limit :
∀ (β θ M : ℝ), 0 < θ → θ < β → β < 1/4 →
  MeanSquareHL4 concreteSS β → IntervalCorrelations concreteSS → 0 < M →
  ∀ (c : Fin 4 → ℝ), (∀ i, c i ∈ Icc (0:ℝ) M) →
  ∀ u v : ℝ, 1 ≤ u → u < v → v ≤ 2 →
  Tendsto (fixedBlockMoment (fun x => Chebyshev.psi x-x) θ 4 c u v) atTop
    (𝓝 ((DyadicProbability.dyadicProbabilityMeasure 1).real (Icc u v)*
      ((1-θ)^2*MomentTransferDefs.brownianW4 c))) := by
  intro β θ M hθ hθβ hβ hMS hcor hM c hc u v hu huv hv
  have hα : 0 < θ / 2 := half_pos hθ
  have hαβ : θ / 2 < β := by linarith
  have hadm : admissible (max 1 M) (fun _ => 0) c := by
    intro i
    exact ⟨le_rfl, (hc i).1, (hc i).2.trans (le_max_right 1 M)⟩
  let B := 3 / Real.log 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw := log_block_bv u v hu huv.le hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : 0 < ε / (B + 1) := div_pos hε (by positivity)
  have hbudget : B * (ε / (B + 1)) < ε := by
    have heq : (B + 1) * (ε / (B + 1)) = ε := by field_simp
    nlinarith
  filter_upwards [real_fourth concreteSS (θ / 2) β (max 1 M)
      hα hαβ hβ concreteSS_empty concreteSS_singleton hMS hcor (le_max_left 1 M)
      (ε / (B + 1)) ht,
    p_power_in_band (θ / 2) θ β (by linarith) hθβ.le,
    eventually_ge_atTop (2 : ℝ)] with X hreal hband hX
  have hX0 : 0 < X := by linarith
  rw [Real.dist_eq, p_block_moment_identity X θ u v 4 c hX0]
  have he := hreal (X ^ θ) hband.1 hband.2 B _ hw (fun _ => 0) c hadm
  rw [p_power_variance X θ (by linarith), p_prefix_w4 c (fun i => (hc i).1),
    p_log_block_mass u v hu huv.le hv] at he
  have hassoc : (DyadicProbability.dyadicProbabilityMeasure 1).real (Icc u v) *
      (1 - θ) ^ 2 * MomentTransferDefs.brownianW4 c =
      (DyadicProbability.dyadicProbabilityMeasure 1).real (Icc u v) *
        ((1 - θ) ^ 2 * MomentTransferDefs.brownianW4 c) := by ring
  rw [hassoc] at he
  exact he.trans_lt hbudget

/-- The Chebyshev error satisfies the third fixed-scale mixed-moment interface. -/
theorem fixed_scale_third :
∀ β θ : ℝ, 0 < θ → θ < β → β < 1/3 →
  MeanSquareHL 3 concreteSS β → IntervalCorrelations concreteSS →
  FixedScaleMixedMoments (fun x => Chebyshev.psi x-x) θ 3 (fun _ => 0) := by
  intro β θ hθ hθβ hβ hMS hcor M hM c hc u v hu huv hv
  simpa only [mul_zero] using
    p_fixed_scale_third_limit β θ M hθ hθβ hβ hMS hcor hM c hc u v hu huv hv

/-- The Chebyshev error satisfies the fourth fixed-scale mixed-moment interface. -/
theorem fixed_scale_fourth :
∀ β θ : ℝ, 0 < θ → θ < β → β < 1/4 →
  MeanSquareHL4 concreteSS β → IntervalCorrelations concreteSS →
  FixedScaleMixedMoments (fun x => Chebyshev.psi x-x) θ 4
    (fun c => (1-θ)^2*MomentTransferDefs.brownianW4 c) := by
  intro β θ hθ hθβ hβ hMS hcor M hM c hc u v hu huv hv
  exact p_fixed_scale_fourth_limit β θ M hθ hθβ hβ hMS hcor hM c hc u v hu huv hv

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
