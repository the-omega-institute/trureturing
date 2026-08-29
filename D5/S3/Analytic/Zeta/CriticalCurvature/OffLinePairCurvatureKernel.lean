/- GID: D5/S3/Analytic/Zeta/CriticalCurvature/OffLinePairCurvatureKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/CriticalCurvature/OffLinePairCurvatureKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A reflection-paired logarithmic potential has a certified slope
     whose axis derivative is the off-line curvature dipole. -/

import Mathlib

/-!
This is the local two-zero model only. It does not identify the model with the
full logarithmic potential of the completed Riemann xi function, and it makes no
zero-reconstruction claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Zeta.CriticalCurvature.OffLinePairCurvatureKernel

/-- Squared distance in the normal-tangential plane from `(a, 0)`. -/
def radialQuadratic (a y u : ℝ) : ℝ :=
  (u - a) ^ 2 + y ^ 2

/-- Half-logarithmic potential of one local zero factor. -/
def radialLogPotential (a y u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (radialQuadratic a y u)

/-- Certified first-derivative field of one radial logarithmic potential. -/
def radialLogSlope (a y u : ℝ) : ℝ :=
  (u - a) / radialQuadratic a y u

/-- Derivative of the radial quadratic. -/
theorem radial_quadratic_hasDerivAt (a y u : ℝ) :
    HasDerivAt (radialQuadratic a y) (2 * (u - a)) u := by
  have hSub : HasDerivAt (fun v : ℝ => v - a) 1 u := by
    simpa using (hasDerivAt_id u).sub_const a
  have hSquare := hSub.pow 2
  have hSum := hSquare.add_const (y ^ 2)
  simpa [radialQuadratic] using hSum

/-- The displayed slope is the ordinary derivative whenever the local factor
is nonzero. -/
theorem radial_log_potential_hasDerivAt
    {a y u : ℝ} (hNonzero : radialQuadratic a y u ≠ 0) :
    HasDerivAt (radialLogPotential a y)
      (radialLogSlope a y u) u := by
  have hLog := (radial_quadratic_hasDerivAt a y u).log hNonzero
  have hScaled := hLog.const_mul (1 / 2 : ℝ)
  convert hScaled using 1
  · rfl
  · unfold radialLogSlope
    ring

/-- Derivative of the certified slope field. -/
theorem radial_log_slope_hasDerivAt
    {a y u : ℝ} (hNonzero : radialQuadratic a y u ≠ 0) :
    HasDerivAt (radialLogSlope a y)
      ((y ^ 2 - (u - a) ^ 2) / (radialQuadratic a y u) ^ 2) u := by
  have hNumerator : HasDerivAt (fun v : ℝ => v - a) 1 u := by
    simpa using (hasDerivAt_id u).sub_const a
  have hDenominator := radial_quadratic_hasDerivAt a y u
  have hQuotient := hNumerator.div hDenominator hNonzero
  convert hQuotient using 1
  · rfl
  · unfold radialQuadratic
    field_simp [hNonzero]
    ring

/-- Reflection-paired local potential centered at tangential height `gamma` and
normal displacement `delta`. -/
def offLinePairPotential (delta gamma u t : ℝ) : ℝ :=
  radialLogPotential delta (t - gamma) u +
    radialLogPotential (-delta) (t - gamma) u

/-- Sum of the two certified first-derivative fields. -/
def offLinePairSlope (delta gamma u t : ℝ) : ℝ :=
  radialLogSlope delta (t - gamma) u +
    radialLogSlope (-delta) (t - gamma) u

/-- Curvature dipole observed on the reflection-fixed axis. -/
def offLinePairCurvatureKernel (delta gamma t : ℝ) : ℝ :=
  2 * ((t - gamma) ^ 2 - delta ^ 2) /
    (((t - gamma) ^ 2 + delta ^ 2) ^ 2)

/-- Positive displacement keeps both local factors nonzero at the fixed axis. -/
theorem radial_quadratic_axis_pos
    {delta y : ℝ} (hDelta : 0 < delta) :
    0 < radialQuadratic delta y 0 ∧
      0 < radialQuadratic (-delta) y 0 := by
  have hDeltaSq : 0 < delta ^ 2 := sq_pos_of_pos hDelta
  constructor <;> unfold radialQuadratic <;> nlinarith [sq_nonneg y]

/-- The paired potential has zero first normal derivative on the fixed axis. -/
theorem off_line_pair_potential_hasDerivAt_axis_zero
    {delta gamma t : ℝ} (hDelta : 0 < delta) :
    HasDerivAt (fun u : ℝ => offLinePairPotential delta gamma u t)
      0 0 := by
  have hPos := radial_quadratic_axis_pos (y := t - gamma) hDelta
  have hMinus := radial_log_potential_hasDerivAt hPos.1.ne'
  have hPlus := radial_log_potential_hasDerivAt hPos.2.ne'
  have hSum := hMinus.add hPlus
  convert hSum using 1
  · rfl
  · unfold radialLogSlope radialQuadratic
    ring

/-- The derivative of the certified first-derivative field at the fixed axis is
exactly the off-line curvature dipole. -/
theorem off_line_pair_slope_hasDerivAt_axis
    {delta gamma t : ℝ} (hDelta : 0 < delta) :
    HasDerivAt (fun u : ℝ => offLinePairSlope delta gamma u t)
      (offLinePairCurvatureKernel delta gamma t) 0 := by
  have hPos := radial_quadratic_axis_pos (y := t - gamma) hDelta
  have hMinus := radial_log_slope_hasDerivAt hPos.1.ne'
  have hPlus := radial_log_slope_hasDerivAt hPos.2.ne'
  have hSum := hMinus.add hPlus
  convert hSum using 1
  · rfl
  · unfold offLinePairCurvatureKernel radialQuadratic
    ring

/-- Center value of the dipole. -/
theorem off_line_pair_curvature_center
    {delta gamma : ℝ} (hDelta : delta ≠ 0) :
    offLinePairCurvatureKernel delta gamma gamma =
      -2 / delta ^ 2 := by
  unfold offLinePairCurvatureKernel
  field_simp [hDelta]
  ring

/-- Right zero crossing at tangential offset `delta`. -/
theorem off_line_pair_curvature_right_zero
    {delta gamma : ℝ} (hDelta : delta ≠ 0) :
    offLinePairCurvatureKernel delta gamma (gamma + delta) = 0 := by
  unfold offLinePairCurvatureKernel
  field_simp [hDelta]
  ring

/-- Left zero crossing at tangential offset `-delta`. -/
theorem off_line_pair_curvature_left_zero
    {delta gamma : ℝ} (hDelta : delta ≠ 0) :
    offLinePairCurvatureKernel delta gamma (gamma - delta) = 0 := by
  unfold offLinePairCurvatureKernel
  field_simp [hDelta]
  ring

/-- The center of a genuine off-axis pair is a negative curvature well. -/
theorem off_line_pair_curvature_center_neg
    {delta gamma : ℝ} (hDelta : 0 < delta) :
    offLinePairCurvatureKernel delta gamma gamma < 0 := by
  rw [off_line_pair_curvature_center hDelta.ne']
  have hSquare : 0 < delta ^ 2 := sq_pos_of_pos hDelta
  exact div_neg_of_neg_of_pos (by norm_num) hSquare

/-- The dipole kernel is even in tangential displacement around its center. -/
theorem off_line_pair_curvature_reflection
    (delta gamma y : ℝ) :
    offLinePairCurvatureKernel delta gamma (gamma - y) =
      offLinePairCurvatureKernel delta gamma (gamma + y) := by
  unfold offLinePairCurvatureKernel
  ring

#print axioms radial_log_potential_hasDerivAt
#print axioms radial_log_slope_hasDerivAt
#print axioms off_line_pair_potential_hasDerivAt_axis_zero
#print axioms off_line_pair_slope_hasDerivAt_axis
#print axioms off_line_pair_curvature_center
#print axioms off_line_pair_curvature_right_zero
#print axioms off_line_pair_curvature_left_zero

end D5.S3.Analytic.Zeta.CriticalCurvature.OffLinePairCurvatureKernel
