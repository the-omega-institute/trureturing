/- GID: D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenSpectralPairUnitarity
   generality: I
   mirror-B: D5/B/S3/Analytic/Zeta/GoldenSpectrum/GoldenSpectralPairUnitarity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every golden reflection-pair transfer is determinant-balanced, while
     its Euclidean isometry is equivalent to the original point lying on the critical line. -/

import D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate
import D5.S3.Analytic.Zeta.GoldenSpectrum.ReflectionPairTransfer

/- Library-search audit trail (2026-08-30):
   * Repository searches for a theorem connecting golden radial charge,
     determinant balance, pair isometry, and critical-line support found no
     exact owner.
   * The two imported owners provide the exact coordinate and abstract transfer
     lemmas; this module proves their typed composition.
   * No completed-zeta zero hypothesis is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenSpectralPairUnitarity

open D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenCriticalCoordinate
open D5.S3.Analytic.Zeta.GoldenSpectrum.ReflectionPairTransfer

/-- Every spectral point defines a determinant-one reciprocal pair transfer. -/
theorem golden_spectral_pair_determinant_one (s : ℂ) :
    Matrix.det (reflectionPairTransfer (goldenRadialCharge s)) = 1 := by
  exact reflection_pair_determinant_one
    (golden_radial_charge_pos s).ne'

/-- Pointwise Euclidean isometry of the reciprocal pair is exactly the
critical-line condition. -/
theorem golden_spectral_pair_isometry_iff (s : ℂ) :
    IsReflectionPairIsometry (goldenRadialCharge s) ↔
      s.re = (1 / 2 : ℝ) := by
  rw [reflection_pair_isometry_iff (golden_radial_charge_pos s)]
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

/-- A point off the critical line gives a determinant-balanced transfer that
fails pointwise isometry. -/
theorem off_critical_pair_balanced_but_not_isometric
    {s : ℂ} (hOff : s.re ≠ (1 / 2 : ℝ)) :
    Matrix.det (reflectionPairTransfer (goldenRadialCharge s)) = 1 ∧
      ¬ IsReflectionPairIsometry (goldenRadialCharge s) := by
  constructor
  · exact golden_spectral_pair_determinant_one s
  · exact (golden_spectral_pair_isometry_iff s).not.mpr hOff

/-- The critical center gives the neutral reciprocal transfer. -/
example :
    IsReflectionPairIsometry
      (goldenRadialCharge ((1 / 2 : ℝ) : ℂ)) := by
  exact (golden_spectral_pair_isometry_iff _).2 (by simp)

#print axioms golden_spectral_pair_determinant_one
#print axioms golden_spectral_pair_isometry_iff
#print axioms off_critical_pair_balanced_but_not_isometric

end D5.S3.Analytic.Zeta.GoldenSpectrum.GoldenSpectralPairUnitarity
