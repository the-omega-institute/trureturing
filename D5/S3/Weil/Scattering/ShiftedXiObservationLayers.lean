/- GID: D5/S3/Weil/Scattering/ShiftedXiObservationLayers
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/ShiftedXiObservationLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Opposite shifted-xi layers are sharp reflections linked by a quotient. -/

import D5.S3.Weil.Scattering.FiniteScatteringCascade
import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open, its `coverage_gids` and receipt lists are
     empty, and no formalization receipt exists. Its four adjacent atoms are
     also residual-open, so none supplies a bound section-neighbor theorem.
   * Exact D5 body-shape search found `shiftedXiScattering`, which already owns
     the source's quotient, and `xi_reading_one_sub_conj`, which owns the
     required reflection-conjugation law. They are reused rather than restated.
     `CriticalCenterCoordinate` transports reflection to center coordinates but
     does not identify the two shifted xi observations.
   * Pinned Mathlib supplies `completedRiemannZeta_one_sub` underneath the frozen
     xi covariance theorem and `div_mul_cancel₀` for regular quotient recovery.
     Searches of the other installed Lean packages found no shifted-xi layer law.
   * The upstream `anthropics/zeta-23-lean` tree at commit
     `2bafb8c88f177284a2123b5fefa2ff84e2365eb6` contains the completed-zeta
     functional equation but no shifted-xi observation or Suzuki-theta layer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Scattering.ShiftedXiObservationLayers

open D5.S3.Weil.Scattering.FiniteScatteringCascade
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
open scoped ComplexConjugate

/-- The positive shifted-xi observation at real depth `omega`. -/
def shiftedXiObservation (omega : ℝ) (z : ℂ) : ℂ :=
  xiReading (1 / 2 + (omega : ℂ) - Complex.I * z)

/-- Sharp reflection of the positive shifted-xi observation. -/
def shiftedXiObservationSharp (omega : ℝ) (z : ℂ) : ℂ :=
  conj (shiftedXiObservation omega (conj z))

/-- At positive observation depth, sharp reflection is the opposite shifted-xi
layer. The existing shifted-xi scattering reading is exactly their quotient;
away from a zero of the positive layer, multiplying the quotient back recovers
the sharp layer. -/
theorem shifted_xi_observation_layers
    (omega : ℝ) (omegaPositive : 0 < omega) (z : ℂ)
    (denominatorNonzero : shiftedXiObservation omega z ≠ 0) :
    shiftedXiObservationSharp omega z =
        xiReading (1 / 2 - (omega : ℂ) - Complex.I * z) ∧
      shiftedXiScattering (omega : ℂ) z =
        shiftedXiObservationSharp omega z / shiftedXiObservation omega z ∧
      shiftedXiScattering (omega : ℂ) z * shiftedXiObservation omega z =
        shiftedXiObservationSharp omega z := by
  have sharpLayer :
      shiftedXiObservationSharp omega z =
        xiReading (1 / 2 - (omega : ℂ) - Complex.I * z) := by
    unfold shiftedXiObservationSharp shiftedXiObservation
    rw [← xi_reading_one_sub_conj]
    congr 1
    simp
    rw [starRingEnd_apply, star_ofNat]
    ring
  have quotientLayer :
      shiftedXiScattering (omega : ℂ) z =
        shiftedXiObservationSharp omega z / shiftedXiObservation omega z := by
    rw [shiftedXiScattering, shiftedXiObservation, sharpLayer]
  refine ⟨sharpLayer, quotientLayer, ?_⟩
  rw [quotientLayer]
  exact div_mul_cancel₀ _ denominatorNonzero

/-- Depth one half at spectral coordinate zero is a regular concrete instance
of both observation-layer identities. -/
theorem positive_depth_observation_witness :
    0 < (1 / 2 : ℝ) ∧
      shiftedXiObservation (1 / 2) 0 ≠ 0 ∧
      shiftedXiObservationSharp (1 / 2) 0 =
          xiReading (1 / 2 - ((1 / 2 : ℝ) : ℂ) - Complex.I * 0) ∧
        shiftedXiScattering (((1 / 2 : ℝ) : ℂ)) 0 =
          shiftedXiObservationSharp (1 / 2) 0 /
            shiftedXiObservation (1 / 2) 0 ∧
        shiftedXiScattering (((1 / 2 : ℝ) : ℂ)) 0 *
            shiftedXiObservation (1 / 2) 0 =
          shiftedXiObservationSharp (1 / 2) 0 := by
  have depthPositive : 0 < (1 / 2 : ℝ) := by norm_num
  have denominatorNonzero : shiftedXiObservation (1 / 2) 0 ≠ 0 := by
    norm_num [shiftedXiObservation, xiReading]
  exact ⟨depthPositive, denominatorNonzero,
    shifted_xi_observation_layers (1 / 2) depthPositive 0 denominatorNonzero⟩

/-- If the denominator regularity premise is dropped, quotient multiplication
can lose a nonzero numerator because Lean totalizes division by zero. -/
theorem zero_denominator_breaks_transition_recovery :
    let numerator : ℂ := 1
    let denominator : ℂ := 0
    denominator = 0 ∧ numerator / denominator * denominator ≠ numerator := by
  norm_num

#print axioms shifted_xi_observation_layers
#print axioms positive_depth_observation_witness
#print axioms zero_denominator_breaks_transition_recovery

end D5.S3.Weil.Scattering.ShiftedXiObservationLayers
