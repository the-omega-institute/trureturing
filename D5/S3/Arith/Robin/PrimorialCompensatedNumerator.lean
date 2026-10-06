/- GID: D5/S3/Arith/Robin/PrimorialCompensatedNumerator
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/PrimorialCompensatedNumerator
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Exact initial-slope compensation pays the actual finite Euler numerator at zero. -/

import D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

/-! The actual finite-cutoff slope, curvature and ratio suppliers are consumed
from their original module. The compensation retains the actual initial slope.
The endpoint is a uniform quadratic zero-end budget, not an integral limit. -/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped BigOperators Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope

namespace D5.S3.Arith.Robin.PrimorialCompensatedNumerator

def actualShiftedRatio (z a v : ℝ) : ℝ :=
  Real.exp (-a * v) * actualRatio z v

theorem actualShiftedRatio_zero (z a : ℝ) :
    actualShiftedRatio z a 0 = 1 := by
  simp only [actualShiftedRatio, mul_zero, Real.exp_zero, actualRatio_zero z, mul_one]

theorem hasDerivAt_actualShiftedRatio {z v : ℝ} (hz : 2 ≤ z) (hv : 0 ≤ v)
    (a : ℝ) :
    HasDerivAt (actualShiftedRatio z a)
      (actualShiftedRatio z a v * (actualSlope z v - a)) v := by
  have hexp := ((hasDerivAt_id v).const_mul (-a)).exp
  have h := hexp.mul (hasDerivAt_actualRatio hz hv)
  apply h.congr_deriv
  unfold actualShiftedRatio
  simp only [id_eq]
  ring

theorem hasDerivAt_actualShiftedRatio_derivative {z v : ℝ}
    (hz : 2 ≤ z) (hv : 0 ≤ v) (a : ℝ) :
    HasDerivAt
      (fun w : ℝ => actualShiftedRatio z a w * (actualSlope z w - a))
      (actualShiftedRatio z a v *
        ((actualSlope z v - a) ^ 2 - actualCurvature z v)) v := by
  have h := (hasDerivAt_actualShiftedRatio hz hv a).mul
    ((hasDerivAt_actualSlope hz hv).sub_const a)
  apply h.congr_deriv
  ring

/-- The linear coefficient is the exact initial finite-cutoff slope. -/
def actualCompensatedNumerator (z a v : ℝ) : ℝ :=
  actualShiftedRatio z a v - 1 + (a - actualSlope z 0) * v

theorem actualCompensatedNumerator_zero (z a : ℝ) :
    actualCompensatedNumerator z a 0 = 0 := by
  simp only [actualCompensatedNumerator, actualShiftedRatio_zero z a, sub_self,
    mul_zero, add_zero]

theorem hasDerivAt_actualCompensatedNumerator {z v : ℝ}
    (hz : 2 ≤ z) (hv : 0 ≤ v) (a : ℝ) :
    HasDerivAt (actualCompensatedNumerator z a)
      (actualShiftedRatio z a v * (actualSlope z v - a) +
        (a - actualSlope z 0)) v := by
  have h := ((hasDerivAt_actualShiftedRatio hz hv a).sub_const 1).add
    ((hasDerivAt_id v).const_mul (a - actualSlope z 0))
  apply h.congr_deriv
  ring

/-- The compensation cancels the actual first derivative, for every finite z. -/
theorem hasDerivAt_actualCompensatedNumerator_zero {z : ℝ}
    (hz : 2 ≤ z) (a : ℝ) :
    HasDerivAt (actualCompensatedNumerator z a) 0 0 := by
  have h := hasDerivAt_actualCompensatedNumerator (v := 0) hz (by norm_num) a
  apply h.congr_deriv
  rw [actualShiftedRatio_zero z a]
  ring

private theorem actualSlope_le_two {z v : ℝ} (hz : 2 ≤ z)
    (hbudget : budget / Real.log z ≤ 1) (hv : 0 ≤ v) :
    actualSlope z v ≤ 2 := by
  have h := actualSlope_first_mertens_uniform hz (by norm_num : (0 : ℝ) ≤ 0)
  change |actualSlope z 0 -
    (∫ b in (0 : ℝ)..1, Real.exp (-(0 : ℝ) * b))| ≤ budget / Real.log z at h
  have hr : (∫ b in (0 : ℝ)..1, Real.exp (-(0 : ℝ) * b)) = 1 := by simp
  rw [hr] at h
  have hupper := (abs_le.mp h).2
  exact (actualSlope_le_initial hz hv).trans (by linarith)

private theorem actualShiftedRatio_second_local_bound {z a V v : ℝ}
    (hz : 2 ≤ z) (hbudget : budget / Real.log z ≤ 1)
    (ha : 0 ≤ a) (haV : a ≤ V) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    |actualShiftedRatio z a v *
      ((actualSlope z v - a) ^ 2 - actualCurvature z v)| ≤
      Real.exp 2 * ((V + 2) ^ 2 + 4) := by
  have hS0 := actualSlope_nonneg hz hv
  have hS2 := actualSlope_le_two hz hbudget hv
  have hT := actualCurvature_bounds hz hv
  have hT4 : actualCurvature z v ≤ 4 := by linarith [hT.2]
  have hV : 0 ≤ V := ha.trans haV
  have hxlo : -(V + 2) ≤ actualSlope z v - a := by linarith
  have hxhi : actualSlope z v - a ≤ V + 2 := by linarith
  have hsq : (actualSlope z v - a) ^ 2 ≤ (V + 2) ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hxhi)
      (by linarith : 0 ≤ (actualSlope z v - a) + (V + 2))
    nlinarith
  have hcoeff : |(actualSlope z v - a) ^ 2 - actualCurvature z v| ≤
      (V + 2) ^ 2 + 4 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (actualSlope z v - a), sq_nonneg (V + 2), hT.1]
  have hF0 := (actualRatio_pos hz hv).le
  have hexp : Real.exp (-a * v) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hQ : actualShiftedRatio z a v ≤ Real.exp 2 := by
    calc
      _ ≤ 1 * actualRatio z v := mul_le_mul_of_nonneg_right hexp hF0
      _ ≤ Real.exp 2 := by simpa only [one_mul] using actualRatio_le_exp_two hz hbudget hv hv1
  have hQ0 : 0 ≤ actualShiftedRatio z a v :=
    mul_nonneg (Real.exp_pos _).le hF0
  rw [abs_mul, abs_of_nonneg hQ0]
  exact mul_le_mul hQ hcoeff (abs_nonneg _) (Real.exp_pos _).le

/-- The zero-end budget for the actual, exactly compensated signed numerator.
This is a local supplier for the forthcoming integral consumer, not that limit. -/
theorem actualCompensatedNumerator_quadratic {z a V v : ℝ}
    (hz : 2 ≤ z) (hbudget : budget / Real.log z ≤ 1)
    (ha : 0 ≤ a) (haV : a ≤ V) (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    |actualCompensatedNumerator z a v| ≤
      Real.exp 2 * ((V + 2) ^ 2 + 4) * v ^ 2 / 2 := by
  let G : ℝ → ℝ := fun w =>
    actualShiftedRatio z a w * (actualSlope z w - a) + (a - actualSlope z 0)
  let H : ℝ := Real.exp 2 * ((V + 2) ^ 2 + 4)
  have hG (w : ℝ) (hw : 0 ≤ w) : HasDerivAt G
      (actualShiftedRatio z a w *
        ((actualSlope z w - a) ^ 2 - actualCurvature z w)) w :=
    (hasDerivAt_actualShiftedRatio_derivative hz hw a).add_const (a - actualSlope z 0)
  have hGzero : G 0 = 0 :=
    (hasDerivAt_actualCompensatedNumerator (v := 0) hz (by norm_num) a).unique
      (hasDerivAt_actualCompensatedNumerator_zero hz a)
  have hGbound : ∀ w ∈ Icc (0 : ℝ) v, ‖G w‖ ≤ H * w := by
    intro w hw
    have hdiff : ∀ t ∈ Icc (0 : ℝ) w, DifferentiableAt ℝ G t :=
      fun t ht => (hG t ht.1).differentiableAt
    have hbound : ∀ t ∈ Icc (0 : ℝ) w, ‖deriv G t‖ ≤ H := by
      intro t ht
      rw [(hG t ht.1).deriv, Real.norm_eq_abs]
      exact actualShiftedRatio_second_local_bound hz hbudget ha haV ht.1
        (ht.2.trans (hw.2.trans hv1))
    have h := (convex_Icc (0 : ℝ) w).norm_image_sub_le_of_norm_deriv_le
      hdiff hbound (x := 0) (y := w) ⟨le_rfl, hw.1⟩ ⟨hw.1, le_rfl⟩
    simpa only [hGzero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hw.1] using h
  have hGc : ContinuousOn G (Icc (0 : ℝ) v) :=
    fun w hw => (hG w hw.1).continuousAt.continuousWithinAt
  have hGI : IntervalIntegrable G volume 0 v := hGc.intervalIntegrable_of_Icc hv
  have hFTC : (∫ w in (0 : ℝ)..v, G w) = actualCompensatedNumerator z a v := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := actualCompensatedNumerator z a) (f' := G)
      (fun w hw => hasDerivAt_actualCompensatedNumerator hz
        (by
          have hw' : w ∈ Icc (0 : ℝ) v := by
            simpa only [uIcc_of_le hv] using hw
          exact hw'.1) a) hGI
    simpa only [actualCompensatedNumerator_zero z a, sub_zero] using h
  have hnorm : ‖∫ w in (0 : ℝ)..v, G w‖ ≤ ∫ w in (0 : ℝ)..v, H * w :=
    intervalIntegral.norm_integral_le_of_norm_le hv
      (Filter.Eventually.of_forall (fun w hw => hGbound w ⟨hw.1.le, hw.2⟩))
      ((continuous_const.mul continuous_id).intervalIntegrable 0 v)
  rw [hFTC, Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    integral_id] at hnorm
  simpa [H, mul_div_assoc] using hnorm

end D5.S3.Arith.Robin.PrimorialCompensatedNumerator
