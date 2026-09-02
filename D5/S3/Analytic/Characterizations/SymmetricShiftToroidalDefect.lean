/- GID: D5/S3/Analytic/Characterizations/SymmetricShiftToroidalDefect
   generality: I
   mirror-B: D5/B/S3/Analytic/Characterizations/SymmetricShiftToroidalDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nonzero toroidal frames expose the exact symmetric-shift xi norm defect. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import D5.S3.Zeros.Symmetry.ZetaConjugationCovariance

/- Library-search audit trail (2026-09-01):
   * Repository searches for Hermite-Biehler defects, symmetric shifted-xi
     energies, finite toroidal frames, normalization ratios, and the body
     shape below found no equivalent declaration. The nearby
     `FiniteToroidalFrameReconstruction` reconstructs xi by an inner-product
     quotient but does not identify a squared-norm ratio.
   * Pinned Mathlib supplies the exact scalar identity `norm_smul` and the
     nonzero denominator facts used below. It has no theorem packaging this
     symmetric-shift defect. Searches of every pinned Lean package found no
     Hermite-Biehler, de Branges, normalized-energy, or toroidal-frame match.
   * Exact frozen D5 dependency hits: `xi_reading_conj` and
     `xi_reading_reflection` identify the minus-shifted reading with the
     Hermite-Biehler sharp of the plus-shifted reading. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Characterizations.SymmetricShiftToroidalDefect

open Complex
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Symmetry.ZetaConjugationCovariance
open scoped ComplexConjugate

noncomputable section

/-- The source point `s_z = 1 / 2 - i z`. -/
def symmetricShiftBase (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) - I * z

/-- The plus-shifted reading at `s_z + omega`. -/
def shiftedPlusReading (xi : ℂ -> ℂ) (omega : ℝ) (z : ℂ) : ℂ :=
  xi (symmetricShiftBase z + (omega : ℂ))

/-- The minus-shifted reading at `s_z - omega`. -/
def shiftedMinusReading (xi : ℂ -> ℂ) (omega : ℝ) (z : ℂ) : ℂ :=
  xi (symmetricShiftBase z - (omega : ℂ))

/-- The Hermite-Biehler sharp operation `f#(z) = conj (f (conj z))`. -/
def hermiteBiehlerSharp (f : ℂ -> ℂ) (z : ℂ) : ℂ :=
  conj (f (conj z))

/-- Squared norm of a scaled frame, normalized by the frame's squared norm. -/
def normalizedFrameEnergy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (amplitude : ℂ) (frame : V) : ℝ :=
  ‖amplitude • frame‖ ^ 2 / ‖frame‖ ^ 2

/-- Difference of the normalized plus and minus shifted frame energies. -/
def toroidalHermiteBiehlerDefect
    {VPlus VMinus : Type*}
    [NormedAddCommGroup VPlus] [NormedSpace ℂ VPlus]
    [NormedAddCommGroup VMinus] [NormedSpace ℂ VMinus]
    (xi : ℂ -> ℂ) (z : ℂ) (omega : ℝ)
    (plusFrame : VPlus) (minusFrame : VMinus) : ℝ :=
  normalizedFrameEnergy (shiftedPlusReading xi omega z) plusFrame -
    normalizedFrameEnergy (shiftedMinusReading xi omega z) minusFrame

private theorem normalized_frame_energy_eq_modulus_sq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (amplitude : ℂ) (frame : V) (frameNonzero : frame ≠ 0) :
    normalizedFrameEnergy amplitude frame = ‖amplitude‖ ^ 2 := by
  rw [normalizedFrameEnergy, norm_smul]
  have denominatorNonzero : ‖frame‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr frameNonzero)
  calc
    (‖amplitude‖ * ‖frame‖) ^ 2 / ‖frame‖ ^ 2 =
        ‖amplitude‖ ^ 2 * ‖frame‖ ^ 2 / ‖frame‖ ^ 2 := by ring
    _ = ‖amplitude‖ ^ 2 := mul_div_cancel_right₀ _ denominatorNonzero

/-- Reflection and conjugation of xi identify the symmetric shifted readings. -/
theorem shifted_minus_reading_eq_sharp_plus (omega : ℝ) (z : ℂ) :
    shiftedMinusReading xiReading omega z =
      hermiteBiehlerSharp (fun w => shiftedPlusReading xiReading omega w) z := by
  rw [hermiteBiehlerSharp, shiftedMinusReading, shiftedPlusReading, ← xi_reading_conj]
  have argumentIdentity :
      conj (symmetricShiftBase (conj z) + (omega : ℂ)) =
        1 - (symmetricShiftBase z - (omega : ℂ)) := by
    apply Complex.ext <;> simp [symmetricShiftBase]
    ring
  rw [argumentIdentity, xi_reading_reflection]

/-- For an upper-half-plane point and a positive symmetric shift, nonzero
toroidal frames cancel from their normalized energies. The resulting defect
is exactly the difference of the squared moduli of the two shifted readings. -/
theorem symmetric_shift_toroidal_hermite_biehler_defect
    {VPlus VMinus : Type*}
    [NormedAddCommGroup VPlus] [NormedSpace ℂ VPlus]
    [NormedAddCommGroup VMinus] [NormedSpace ℂ VMinus]
    (z : ℂ) (omega : ℝ)
    (plusFrame : VPlus) (minusFrame : VMinus)
    (upperHalfPlane : 0 < z.im) (_positiveShift : 0 < omega)
    (plusFrameNonzero : plusFrame ≠ 0)
    (minusFrameNonzero : minusFrame ≠ 0) :
    shiftedMinusReading xiReading omega z =
        hermiteBiehlerSharp (fun w => shiftedPlusReading xiReading omega w) z ∧
      (1 / 2 : ℝ) < (symmetricShiftBase z).re ∧
        toroidalHermiteBiehlerDefect xiReading z omega plusFrame minusFrame =
          ‖shiftedPlusReading xiReading omega z‖ ^ 2 -
            ‖shiftedMinusReading xiReading omega z‖ ^ 2 := by
  constructor
  · exact shifted_minus_reading_eq_sharp_plus omega z
  constructor
  · norm_num [symmetricShiftBase, Complex.mul_re]
    linarith
  · unfold toroidalHermiteBiehlerDefect
    rw [normalized_frame_energy_eq_modulus_sq _ _ plusFrameNonzero,
      normalized_frame_energy_eq_modulus_sq _ _ minusFrameNonzero]

-- A one-dimensional nonzero frame makes both sides of the defect identity equal three.
example :
    toroidalHermiteBiehlerDefect id I (1 / 2 : ℝ) (1 : ℂ) (1 : ℂ) =
        ‖shiftedPlusReading id (1 / 2 : ℝ) I‖ ^ 2 -
          ‖shiftedMinusReading id (1 / 2 : ℝ) I‖ ^ 2 ∧
      toroidalHermiteBiehlerDefect id I (1 / 2 : ℝ) (1 : ℂ) (1 : ℂ) = 3 := by
  norm_num [toroidalHermiteBiehlerDefect, normalizedFrameEnergy,
    shiftedPlusReading, shiftedMinusReading, symmetricShiftBase, Complex.norm_def]

-- With a zero plus frame, the left side is minus one while the right side remains three.
example :
    toroidalHermiteBiehlerDefect id I (1 / 2 : ℝ) (0 : ℂ) (1 : ℂ) ≠
        ‖shiftedPlusReading id (1 / 2 : ℝ) I‖ ^ 2 -
          ‖shiftedMinusReading id (1 / 2 : ℝ) I‖ ^ 2 ∧
      toroidalHermiteBiehlerDefect id I (1 / 2 : ℝ) (0 : ℂ) (1 : ℂ) = -1 ∧
        ‖shiftedPlusReading id (1 / 2 : ℝ) I‖ ^ 2 -
          ‖shiftedMinusReading id (1 / 2 : ℝ) I‖ ^ 2 = 3 := by
  norm_num [toroidalHermiteBiehlerDefect, normalizedFrameEnergy,
    shiftedPlusReading, shiftedMinusReading, symmetricShiftBase, Complex.norm_def]

#print axioms symmetric_shift_toroidal_hermite_biehler_defect

end

end D5.S3.Analytic.Characterizations.SymmetricShiftToroidalDefect
