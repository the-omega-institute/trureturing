/- GID: D5/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaLinear/OfflineZeroGeometricMonodromy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realize offline-zero characters as hyperbolic golden-period monodromies. -/

import D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom has empty `coverage_gids` and no formalization receipt. Repository
     searches for offline-zero characters, normalized zero modes, Floquet
     monodromy, hyperbolic discriminants, and golden log periods found the
     character and radial-phase factorization in `OfflineZeroCharacter`, but no
     golden-period two-branch monodromy or its classification. This module
     imports and reuses that character instead of defining a second mode.
   * The nearest D5 discriminant result, `free_transfer_power_discriminant`, is
     about powers of a different Chebyshev transfer matrix. Pinned Mathlib
     supplies the reusable general notions `Matrix.discr_fin_two` and
     `Matrix.IsHyperbolic`, as well as real `rpow`, `sinh`, and golden-ratio
     lemmas; it has no declaration packaging the specialization below.
   * Loogle returned `Matrix.discr_of_card_eq_two` and `Matrix.discr_fin_two`.
     LeanSearch returned no response, and searches of the installed admissible
     third-party Lean packages found no matching Floquet or offline-zero result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.OfflineZeroGeometricMonodromy

open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening

/-- The golden logarithmic period used to sample the Mellin character. -/
def goldenMellinPeriod : ℝ :=
  2 * Real.log Real.goldenRatio

/-- The reciprocal radial branches of an offline-zero character after one
golden logarithmic period. -/
def offlineZeroMonodromy (rho : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.exp (criticalDisplacement rho * goldenMellinPeriod), 0;
     0, Real.exp (-(criticalDisplacement rho * goldenMellinPeriod))]

/-- The exponential monodromy entries are the source's real golden powers. -/
theorem offline_zero_monodromy_eq_golden_rpow (rho : ℂ) :
    offlineZeroMonodromy rho =
      !![Real.goldenRatio ^ (2 * criticalDisplacement rho), 0;
         0, Real.goldenRatio ^ (-(2 * criticalDisplacement rho))] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [offlineZeroMonodromy, goldenMellinPeriod,
      Real.rpow_def_of_pos Real.goldenRatio_pos] <;>
    ring

/-- Reciprocal reflection branches give determinant one. -/
theorem offline_zero_monodromy_det (rho : ℂ) :
    Matrix.det (offlineZeroMonodromy rho) = 1 := by
  rw [Matrix.det_fin_two]
  simp [offlineZeroMonodromy, ← Real.exp_add]

private theorem exp_pair_discriminant (x : ℝ) :
    (Real.exp x + Real.exp (-x)) ^ 2 -
        4 * (Real.exp x * Real.exp (-x)) =
      4 * Real.sinh x ^ 2 := by
  have hProduct : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [Real.sinh_eq]
  nlinarith [hProduct]

/-- Formula (1109.3): the trace discriminant is the square of the radial
hyperbolic sine. -/
theorem offline_zero_monodromy_discriminant (rho : ℂ) :
    (offlineZeroMonodromy rho).discr =
      4 * Real.sinh
        (2 * criticalDisplacement rho * Real.log Real.goldenRatio) ^ 2 := by
  have hPeriod :
      criticalDisplacement rho * goldenMellinPeriod =
        2 * criticalDisplacement rho * Real.log Real.goldenRatio := by
    simp only [goldenMellinPeriod]
    ring
  rw [← hPeriod]
  rw [Matrix.discr_fin_two]
  simpa [offlineZeroMonodromy, Matrix.trace_fin_two, Matrix.det_fin_two] using
    exp_pair_discriminant (criticalDisplacement rho * goldenMellinPeriod)

/-- The character is on the unitary boundary exactly when its radial
displacement vanishes. -/
theorem offline_zero_unitary_boundary_iff (rho : ℂ) :
    IsUnitary (offlineZeroCharacter rho) ↔ criticalDisplacement rho = 0 := by
  rw [offline_zero_character_unitary_iff, criticalDisplacement, sub_eq_zero]

/-- The monodromy is hyperbolic exactly away from the unitary boundary. -/
theorem offline_zero_monodromy_hyperbolic_iff (rho : ℂ) :
    (offlineZeroMonodromy rho).IsHyperbolic ↔
      criticalDisplacement rho ≠ 0 := by
  rw [Matrix.IsHyperbolic, offline_zero_monodromy_discriminant]
  have hLog : Real.log Real.goldenRatio ≠ 0 :=
    (Real.log_pos Real.one_lt_goldenRatio).ne'
  constructor
  · intro hPositive hDisplacement
    rw [hDisplacement] at hPositive
    norm_num at hPositive
  · intro hDisplacement
    have hArgument :
        2 * criticalDisplacement rho * Real.log Real.goldenRatio ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hDisplacement) hLog
    exact mul_pos (by norm_num)
      (sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hArgument))

/-- Formulas (1109.1)--(1109.3) and the boundary/bulk dichotomy, with the
spectral mode reused from `offlineZeroCharacter`. The source's final Solenoid
interpretation is not promoted to an unproved uniqueness or maximality claim. -/
theorem offline_zero_geometric_definition (rho : ℂ) (time : ℝ) :
    offlineZeroCharacter rho (Multiplicative.ofAdd time) =
        Complex.exp (((criticalDisplacement rho * time : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((rho.im * time : ℝ) : ℂ)) ∧
      offlineZeroMonodromy rho =
        !![Real.goldenRatio ^ (2 * criticalDisplacement rho), 0;
           0, Real.goldenRatio ^ (-(2 * criticalDisplacement rho))] ∧
      Matrix.det (offlineZeroMonodromy rho) = 1 ∧
      (offlineZeroMonodromy rho).discr =
        4 * Real.sinh
          (2 * criticalDisplacement rho * Real.log Real.goldenRatio) ^ 2 ∧
      (IsUnitary (offlineZeroCharacter rho) ↔ criticalDisplacement rho = 0) ∧
      ((offlineZeroMonodromy rho).IsHyperbolic ↔
        criticalDisplacement rho ≠ 0) := by
  exact ⟨offline_zero_character_factorization rho time,
    offline_zero_monodromy_eq_golden_rpow rho,
    offline_zero_monodromy_det rho,
    offline_zero_monodromy_discriminant rho,
    offline_zero_unitary_boundary_iff rho,
    offline_zero_monodromy_hyperbolic_iff rho⟩

/-- The geometric definition is realized by a genuinely nonunitary character
whose golden-period monodromy is hyperbolic. -/
theorem exists_offline_zero_geometric_realization :
    ∃ rho : ℂ,
      ¬IsUnitary (offlineZeroCharacter rho) ∧
        (offlineZeroMonodromy rho).IsHyperbolic := by
  rcases exists_nonunitary_offline_zero_character with ⟨rho, hNonunitary⟩
  refine ⟨rho, hNonunitary, ?_⟩
  rw [offline_zero_monodromy_hyperbolic_iff]
  exact (offline_zero_character_nonunitary_iff rho).mp hNonunitary

#print axioms offline_zero_geometric_definition
#print axioms exists_offline_zero_geometric_realization

end D5.S3.Weil.ZetaLinear.OfflineZeroGeometricMonodromy
