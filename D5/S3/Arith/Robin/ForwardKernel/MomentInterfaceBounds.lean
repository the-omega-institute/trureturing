/- GID: D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even-moment bounds normalize under logarithmic dyadic sampling. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds
import D5.S3.Arith.Robin.ForwardKernel.MovingIncrementVariance

/-! Shared normalization of even moving-increment moments. -/

namespace D5.S3.Arith.Robin.ForwardKernel.MomentInterfaceBounds

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer MomentTransferDefs DyadicProbability

noncomputable section
set_option autoImplicit false

/-- A raw even-moment bound yields a uniform normalized moment bound under
logarithmic dyadic sampling, with the factor `1 / log 2`. -/
theorem normalized_even_moment_bound
    {E : ℝ → ℝ} {θ K : ℝ} {m : ℕ}
    (hE : LocallyBoundedMeasurable E)
    (hθ : 0 ≤ θ) (_hK : 0 ≤ K)
    (hraw :
      ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x in X..(2 * X),
          |increment E (s * x ^ θ) x| ^ (2 * m)) ≤
            K * X * (X ^ θ * Real.log X) ^ m) :
    ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
      (∫ x, |dyadicB E θ s x| ^ (2 * m)
        ∂dyadicProbabilityMeasure X) ≤ K / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [hraw, eventually_gt_atTop (1 : ℝ)] with X hraw hX
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hXX : X ≤ 2 * X := by linarith
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ
  have hscale : 0 < X ^ θ * Real.log X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  intro s hs
  have hi : IntegrableOn (fun x => |increment E (s * x ^ θ) x| ^ (2 * m))
      (Icc X (2 * X)) := by
    simpa only [abs_pow, id_eq, Pi.mul_apply, IntegrableOn] using
      (VarianceTransfer.increment_pow_integrableOn (μ := volume) hE
        (K := Icc X (2 * X)) isCompact_Icc (continuous_const.mul hpow)
        continuous_id (2 * m)).abs
  have hpoint (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      |dyadicB E θ s x| ^ (2 * m) / x ≤
        |increment E (s * x ^ θ) x| ^ (2 * m) /
          (X * (X ^ θ * Real.log X) ^ m) := by
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hlog : 0 ≤ Real.log x := (Real.log_pos (hX.trans_le hx.1)).le
    have hmono : X ^ θ * Real.log X ≤ x ^ θ * Real.log x :=
      mul_le_mul (Real.rpow_le_rpow hX0.le hx.1 hθ)
        (Real.log_le_log hX0 hx.1) (Real.log_pos hX).le (Real.rpow_nonneg hx0.le _)
    have hsqrt : Real.sqrt (x ^ θ * Real.log x) ^ (2 * m) =
        (x ^ θ * Real.log x) ^ m := by
      rw [pow_mul, Real.sq_sqrt (mul_nonneg (Real.rpow_nonneg hx0.le _) hlog)]
    rw [dyadicB, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_pow, hsqrt,
      div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc
      X * (X ^ θ * Real.log X) ^ m ≤ x * (x ^ θ * Real.log x) ^ m :=
        mul_le_mul hx.1 (pow_le_pow_left₀ hscale.le hmono m)
          (pow_nonneg hscale.le _) hx0.le
      _ = _ := by ring
  have hint : (∫ x in X..(2 * X), |dyadicB E θ s x| ^ (2 * m) / x) ≤
      (∫ x in X..(2 * X), |increment E (s * x ^ θ) x| ^ (2 * m)) /
        (X * (X ^ θ * Real.log X) ^ m) := by
    rw [intervalIntegral.integral_of_le hXX, intervalIntegral.integral_of_le hXX,
      ← integral_div]
    apply integral_mono_of_nonneg
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact div_nonneg (by positivity) (hX0.trans hx.1).le)
      ((hi.mono_set Ioc_subset_Icc_self).div_const _)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hpoint x ⟨hx.1.le, hx.2⟩
  rw [dyadicProbabilityMeasure_integral hX0 _]
  apply (div_le_div_of_nonneg_right
    (hint.trans (div_le_div_of_nonneg_right (hraw s hs) (by positivity))) hl2.le).trans_eq
  field_simp [hX0.ne', (ne_of_gt (pow_pos hscale m)), hl2.ne']

/-- A variance asymptotic on an exponent band bounds the second absolute
moments of normalized moving increments uniformly over the unit interval. -/
theorem second_moment_bound_interface
    {E : ℝ → ℝ} {α θ β : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (hV : CumulativeVarianceBandAsymptoticFor E α β) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ X : ℝ in atTop, ∀ s ∈ Icc (0 : ℝ) 1,
        (∫ x, |dyadicB E θ s x| ^ 2
          ∂dyadicProbabilityMeasure X) ≤ C := by
  obtain ⟨K, hK, hinc⟩ :=
    MovingIncrementVariance.moving_increment_square_bound hE hB hV
  refine ⟨K / Real.log 2, div_nonneg hK.le (Real.log_pos (by norm_num)).le, ?_⟩
  apply normalized_even_moment_bound (m := 1) hE (hB.1.trans hB.2.1).le hK.le
  filter_upwards [hinc] with X hinc
  intro s hs
  simpa only [Nat.mul_one, pow_one, sq_abs, mul_assoc] using hinc s hs

end
end D5.S3.Arith.Robin.ForwardKernel.MomentInterfaceBounds
