/- GID: D5/S3/Weil/ZetaBridge/RhZeroModeUnitarity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/RhZeroModeUnitarity
   mirror-E: none(waiver:conditional-zero-character-bridge-only)
   anchors: []
   digest: Phase-flattened zero modes are identically one exactly on the critical line, and RH forces this modewise for every supplied ZeroData zero. -/

import D5.S3.Weil.ZetaBridge.RhLocatesZeroData
import D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

/-!
Functional reflection already supplies reciprocal radial branches. This module
formalizes the stronger pointwise condition relevant to RH: after removing the
common ordinate phase, one branch is identically one exactly when its radial
displacement vanishes. For a supplied exhaustive `ZeroData`, RH therefore
forces every enumerated zero character to be unitary and every phase-flattened
mode to be one.

No canonical inhabitant of `ZeroData`, prime-to-zero spectral operator, Weil
positivity implication, or proof of RH is constructed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.RhLocatesZeroData
open D5.S3.Weil.ZetaLinear.ReflectedZeroModePhaseFlattening
open D5.S3.Weil.ZetaLinear.OfflineZeroCharacter

/-- A phase-flattened zero mode is identically one exactly when the point lies
on the critical line. -/
theorem phase_flattened_zero_mode_one_iff_critical_line (rho : ℂ) :
    (∀ time : ℝ, phaseFlattenedZeroMode rho time = 1) ↔
      rho.re = criticalAbscissa := by
  constructor
  · intro hflat
    have hnorm := congrArg norm (hflat 1)
    rw [phase_flattened_zero_mode_eq_radial,
      radial_zero_mode_norm] at hnorm
    have hexponent : -(criticalDisplacement rho * 1) = 0 := by
      apply (Real.exp_eq_one_iff _).mp
      simpa using hnorm
    simp [criticalDisplacement] at hexponent
    linarith
  · intro hline time
    rw [phase_flattened_zero_mode_eq_radial]
    simp [radialZeroMode, criticalDisplacement, hline]

/-- For supplied zero data, modewise radial flatness is exactly pointwise
critical-line location of the enumerated zeros. -/
theorem zeroData_modewise_flat_iff_on_critical_line (Z : ZeroData) :
    (∀ n : ℕ, ∀ time : ℝ,
      phaseFlattenedZeroMode (Z.zero n) time = 1) ↔
    (∀ n : ℕ, (Z.zero n).re = criticalAbscissa) := by
  constructor
  · intro hflat n
    exact (phase_flattened_zero_mode_one_iff_critical_line (Z.zero n)).mp
      (hflat n)
  · intro hline n
    exact (phase_flattened_zero_mode_one_iff_critical_line (Z.zero n)).mpr
      (hline n)

/-- Modewise radial flatness and modewise unitarity are the same condition on
supplied zero data. -/
theorem zeroData_modewise_flat_iff_unitary (Z : ZeroData) :
    (∀ n : ℕ, ∀ time : ℝ,
      phaseFlattenedZeroMode (Z.zero n) time = 1) ↔
    (∀ n : ℕ, IsUnitary (offlineZeroCharacter (Z.zero n))) := by
  rw [zeroData_modewise_flat_iff_on_critical_line]
  constructor
  · intro hline n
    exact (offline_zero_character_unitary_iff (Z.zero n)).2 (hline n)
  · intro hunitary n
    exact (offline_zero_character_unitary_iff (Z.zero n)).1 (hunitary n)

/-- RH forces every supplied zero character to be unitary. -/
theorem rh_implies_zeroData_offline_characters_unitary
    (hRH : RiemannHypothesis) (Z : ZeroData) :
    ∀ n : ℕ, IsUnitary (offlineZeroCharacter (Z.zero n)) := by
  intro n
  exact (offline_zero_character_unitary_iff (Z.zero n)).2
    (zeroData_zero_on_critical_line_of_rh hRH Z n)

/-- RH forces every supplied phase-flattened zero mode to equal one at every
scale-time. -/
theorem rh_implies_zeroData_phase_flattened_modes_one
    (hRH : RiemannHypothesis) (Z : ZeroData) :
    ∀ n : ℕ, ∀ time : ℝ,
      phaseFlattenedZeroMode (Z.zero n) time = 1 := by
  exact (zeroData_modewise_flat_iff_unitary Z).2
    (rh_implies_zeroData_offline_characters_unitary hRH Z)

#print axioms phase_flattened_zero_mode_one_iff_critical_line
#print axioms zeroData_modewise_flat_iff_on_critical_line
#print axioms zeroData_modewise_flat_iff_unitary
#print axioms rh_implies_zeroData_offline_characters_unitary
#print axioms rh_implies_zeroData_phase_flattened_modes_one

end D5.S3.Weil.ZetaBridge.RhZeroModeUnitarity
