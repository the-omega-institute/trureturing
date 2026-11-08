/- GID: D5/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-moment band bounds control normalized dyadic increments. -/

import D5.S3.Arith.Robin.ForwardKernel.MomentTransferDefs
import D5.S3.Arith.Robin.ForwardKernel.FourthMomentMovingBounds

/-! The fourth absolute moment bound in the dyadic moment interface. -/

namespace D5.S3.Arith.Robin.ForwardKernel.FourthMomentInterfaceBridge

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer FourthMomentBandDefs
open MomentTransferDefs DyadicProbability

noncomputable section
set_option autoImplicit false

/-- A fourth-moment bound on an exponent band bounds the fourth absolute moments
of all normalized moving increments, uniformly in their unit profile parameter. -/
theorem fourth_moment_bound_interface
    {E : ℝ → ℝ} {α θ β C₄ : ℝ}
    (hE : LocallyBoundedMeasurable E)
    (hB : ValidBand α θ β)
    (h₄ : FourthMomentBandBoundFor E α β C₄) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ s ∈ Icc (0 : ℝ) 1,
          (∫ x, |dyadicB E θ s x| ^ 4
            ∂dyadicProbabilityMeasure X) ≤ C := by
  obtain ⟨K, hK, hinc⟩ :=
    FourthMomentMovingBounds.moving_increment_fourth_moment_bound hB
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(K / Real.log 2) * C₄, mul_nonneg (div_nonneg hK.le hl2.le) h₄.1, ?_⟩
  filter_upwards [hinc hE h₄, eventually_gt_atTop (1 : ℝ)] with X hinc hX
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hXX : X ≤ 2 * X := by linarith
  have hθ0 : 0 < θ := hB.1.trans hB.2.1
  have hpow : Continuous (fun x : ℝ => x ^ θ) := Real.continuous_rpow_const hθ0.le
  have hscale : 0 < X ^ θ * Real.log X :=
    mul_pos (Real.rpow_pos_of_pos hX0 _) (Real.log_pos hX)
  intro s hs
  have hi : IntegrableOn (fun x => |increment E (s * x ^ θ) x| ^ 4)
      (Icc X (2 * X)) := by
    simpa only [abs_pow, id_eq, Pi.mul_apply, IntegrableOn] using
      (FourthMomentMovingBounds.increment_pow_integrableOn (μ := volume) hE
        (K := Icc X (2 * X)) isCompact_Icc (continuous_const.mul hpow)
        continuous_id 4).abs
  have hpoint (x : ℝ) (hx : x ∈ Icc X (2 * X)) :
      |dyadicB E θ s x| ^ 4 / x ≤
        |increment E (s * x ^ θ) x| ^ 4 / (X * (X ^ θ * Real.log X) ^ 2) := by
    have hx0 : 0 < x := hX0.trans_le hx.1
    have hlog : 0 ≤ Real.log x := (Real.log_pos (hX.trans_le hx.1)).le
    have hmono : X ^ θ * Real.log X ≤ x ^ θ * Real.log x :=
      mul_le_mul (Real.rpow_le_rpow hX0.le hx.1 hθ0.le)
        (Real.log_le_log hX0 hx.1) (Real.log_pos hX).le (Real.rpow_nonneg hx0.le _)
    have hsqrt : Real.sqrt (x ^ θ * Real.log x) ^ 4 = (x ^ θ * Real.log x) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul,
        Real.sq_sqrt (mul_nonneg (Real.rpow_nonneg hx0.le _) hlog)]
    rw [dyadicB, abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_pow, hsqrt,
      div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    calc
      X * (X ^ θ * Real.log X) ^ 2 ≤ x * (x ^ θ * Real.log x) ^ 2 :=
        mul_le_mul hx.1 (pow_le_pow_left₀ hscale.le hmono 2) (sq_nonneg _) hx0.le
      _ = _ := by ring
  have hint : (∫ x in X..(2 * X), |dyadicB E θ s x| ^ 4 / x) ≤
      (∫ x in X..(2 * X), |increment E (s * x ^ θ) x| ^ 4) /
        (X * (X ^ θ * Real.log X) ^ 2) := by
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
    (hint.trans (div_le_div_of_nonneg_right (hinc s hs) (by positivity))) hl2.le).trans_eq
  field_simp [hX0.ne', (Real.rpow_pos_of_pos hX0 θ).ne', (Real.log_pos hX).ne',
    hl2.ne']

end
end D5.S3.Arith.Robin.ForwardKernel.FourthMomentInterfaceBridge
