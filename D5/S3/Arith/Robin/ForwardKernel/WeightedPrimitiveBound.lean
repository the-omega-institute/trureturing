/- GID: D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded primitives control integrals against continuously differentiable weights. -/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! Integration by parts for integrable functions with uniformly bounded primitives. -/

namespace D5.S3.Arith.Robin.ForwardKernel.WeightedPrimitiveBound

open Set MeasureTheory

noncomputable section
set_option autoImplicit false

/-- Integration by parts transfers a uniform primitive bound to a smooth weight. -/
theorem weighted_integral_le_of_primitive_bound
    {f W : ℝ → ℝ} {A B K : ℝ}
    (hAB : A ≤ B)
    (hf : IntervalIntegrable f volume A B)
    (hW : ContDiffOn ℝ 1 W (uIcc A B))
    (_hK : 0 ≤ K)
    (hF : ∀ y ∈ Icc A B, |∫ x in A..y, f x| ≤ K) :
    |∫ x in A..B, W x * f x| ≤
      K * (|W B| + ∫ x in A..B, |deriv W x|) := by
  let F : ℝ → ℝ := fun y => ∫ x in A..y, f x
  have hFac : AbsolutelyContinuousOnInterval F A B :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hWac := hW.absolutelyContinuousOnInterval
  have heq : (∫ x in A..B, W x * f x) =
      W B * F B - ∫ x in A..B, deriv W x * F x := by
    have he : (∫ x in A..B, W x * f x) =
        ∫ x in A..B, W x * deriv F x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxu
      rw [(hx (uIoc_subset_uIcc hxu) A (by simp)).deriv]
    rw [he, hWac.integral_mul_deriv_eq_deriv_mul hFac]
    simp [F]
  have hi := hWac.intervalIntegrable_deriv.mul_continuousOn hFac.continuousOn
  have hbound : |∫ x in A..B, deriv W x * F x| ≤
      K * ∫ x in A..B, |deriv W x| := by
    calc
      _ ≤ ∫ x in A..B, |deriv W x * F x| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun x => deriv W x * F x) hAB
      _ ≤ ∫ x in A..B, K * |deriv W x| := by
        apply intervalIntegral.integral_mono_on hAB hi.abs
          (hWac.intervalIntegrable_deriv.abs.const_mul K)
        intro x hx
        rw [abs_mul, mul_comm K]
        exact mul_le_mul_of_nonneg_left (hF x hx) (abs_nonneg _)
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [heq]
  calc
    _ ≤ |W B * F B| + |∫ x in A..B, deriv W x * F x| := abs_sub _ _
    _ ≤ |W B| * K + K * ∫ x in A..B, |deriv W x| := by
      rw [abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hF B (right_mem_Icc.mpr hAB)) (abs_nonneg _)) hbound
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.WeightedPrimitiveBound
