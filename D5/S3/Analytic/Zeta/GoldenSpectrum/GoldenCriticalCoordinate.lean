/- GID: D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalCoordinate
   generality: I
   mirror-B: D5/B/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden exponentiation sends the critical line to the unit circle and
     intertwines completed reflection with reciprocal conjugation. -/

import Mathlib

/- Library-search audit trail (2026-08-30):
   * Repository searches for a golden exponential critical coordinate, a
     `varphi^(2*s-1)` unit-circle criterion, and reciprocal-conjugate reflection
     found no exact D5 owner.
   * Existing toroidal and Cayley owners encode other critical-line charts and
     are not restated here.
   * Pinned Mathlib supplies `Complex.norm_exp`, `Complex.exp_conj`,
     `Complex.exp_neg`, `Real.exp_eq_one_iff`, and golden-ratio inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate

open scoped ComplexConjugate goldenRatio

/-- The positive logarithmic length of one orientation-preserving golden scale
cycle. -/
def goldenScaleLength : ℝ :=
  2 * Real.log Real.goldenRatio

/-- Completed reflection about the critical line. -/
def criticalReflection (s : ℂ) : ℂ :=
  1 - conj s

/-- Exponential coordinate centered on `Re s = 1/2` and normalized by the
golden scale length. -/
def goldenCriticalCoordinate (s : ℂ) : ℂ :=
  Complex.exp ((goldenScaleLength : ℂ) * (s - (1 / 2 : ℂ)))

/-- Radial charge of a spectral point in the golden coordinate. -/
def goldenRadialCharge (s : ℂ) : ℝ :=
  Real.exp (goldenScaleLength * (s.re - (1 / 2 : ℝ)))

/-- The golden scale length is strictly positive. -/
theorem golden_scale_length_pos :
    0 < goldenScaleLength := by
  unfold goldenScaleLength
  have hLog : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  linarith

/-- The radial charge is always positive. -/
theorem golden_radial_charge_pos (s : ℂ) :
    0 < goldenRadialCharge s := by
  exact Real.exp_pos _

/-- The complex norm of the golden coordinate is exactly its radial charge. -/
theorem norm_golden_critical_coordinate (s : ℂ) :
    ‖goldenCriticalCoordinate s‖ = goldenRadialCharge s := by
  simp [goldenCriticalCoordinate, goldenRadialCharge, goldenScaleLength,
    Complex.norm_exp, Complex.mul_re]

/-- The critical line is exactly the unit circle in the golden coordinate. -/
theorem norm_golden_critical_coordinate_eq_one_iff (s : ℂ) :
    ‖goldenCriticalCoordinate s‖ = 1 ↔
      s.re = (1 / 2 : ℝ) := by
  rw [norm_golden_critical_coordinate]
  unfold goldenRadialCharge
  rw [Real.exp_eq_one_iff]
  constructor
  · intro hProduct
    rcases mul_eq_zero.mp hProduct with hLength | hCentered
    · exact (golden_scale_length_pos.ne' hLength).elim
    · linarith
  · intro hCritical
    rw [hCritical]
    ring

/-- Reflection in the critical line inverts the radial charge. -/
theorem golden_radial_charge_reflection (s : ℂ) :
    goldenRadialCharge (criticalReflection s) =
      (goldenRadialCharge s)⁻¹ := by
  unfold goldenRadialCharge criticalReflection
  rw [← Real.exp_neg]
  congr 1
  simp
  ring

/-- Every reflected pair is globally balanced in radial charge. -/
theorem golden_reflection_pair_charge_product (s : ℂ) :
    goldenRadialCharge s *
      goldenRadialCharge (criticalReflection s) = 1 := by
  rw [golden_radial_charge_reflection]
  exact mul_inv_cancel₀ (golden_radial_charge_pos s).ne'

/-- Completed reflection becomes reciprocal conjugation in the golden
exponential coordinate. -/
theorem golden_critical_coordinate_reflection (s : ℂ) :
    goldenCriticalCoordinate (criticalReflection s) =
      (conj (goldenCriticalCoordinate s))⁻¹ := by
  unfold goldenCriticalCoordinate criticalReflection
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  apply Complex.ext <;> simp [goldenScaleLength] <;> ring

/-- The open critical strip maps to the golden annulus. -/
theorem golden_annulus_bounds {s : ℂ}
    (hLeft : 0 < s.re) (hRight : s.re < 1) :
    Real.goldenRatio⁻¹ < ‖goldenCriticalCoordinate s‖ ∧
      ‖goldenCriticalCoordinate s‖ < Real.goldenRatio := by
  rw [norm_golden_critical_coordinate]
  unfold goldenRadialCharge goldenScaleLength
  have hLog : 0 < Real.log Real.goldenRatio :=
    Real.log_pos Real.one_lt_goldenRatio
  have hLowerExponent :
      -Real.log Real.goldenRatio <
        2 * Real.log Real.goldenRatio * (s.re - (1 / 2 : ℝ)) := by
    nlinarith
  have hUpperExponent :
      2 * Real.log Real.goldenRatio * (s.re - (1 / 2 : ℝ)) <
        Real.log Real.goldenRatio := by
    nlinarith
  constructor
  · calc
      Real.goldenRatio⁻¹ =
          Real.exp (-Real.log Real.goldenRatio) := by
            rw [Real.exp_neg, Real.exp_log Real.goldenRatio_pos]
      _ < Real.exp
          (2 * Real.log Real.goldenRatio * (s.re - (1 / 2 : ℝ))) :=
            (Real.exp_lt_exp).2 hLowerExponent
  · calc
      Real.exp
          (2 * Real.log Real.goldenRatio * (s.re - (1 / 2 : ℝ))) <
          Real.exp (Real.log Real.goldenRatio) :=
            (Real.exp_lt_exp).2 hUpperExponent
      _ = Real.goldenRatio := Real.exp_log Real.goldenRatio_pos

/-- The unit-circle criterion has an explicit inhabitant. -/
example :
    ‖goldenCriticalCoordinate ((1 / 2 : ℝ) : ℂ)‖ = 1 := by
  exact (norm_golden_critical_coordinate_eq_one_iff _).2 (by simp)

#print axioms golden_scale_length_pos
#print axioms norm_golden_critical_coordinate
#print axioms norm_golden_critical_coordinate_eq_one_iff
#print axioms golden_radial_charge_reflection
#print axioms golden_reflection_pair_charge_product
#print axioms golden_critical_coordinate_reflection
#print axioms golden_annulus_bounds

end D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate
