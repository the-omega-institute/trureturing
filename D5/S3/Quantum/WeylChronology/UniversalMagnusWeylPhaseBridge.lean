/- GID: D5/S3/Quantum/WeylChronology/UniversalMagnusWeylPhaseBridge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:cross-representation-adapter)
   anchors: []
   digest: The universal tensor/free-Lie degree-two chronology maps to the same integer center that controls the concrete Weyl phase. -/

import D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
import D5.S3.Observer.Chronology.StepTwoFreeLieBridge

/-!
# Universal Magnus to concrete Weyl phase

The chronology library already owns a universal step-two tensor signature, its
primitive Magnus logarithm, a represented associative shadow and a free-Lie
interpretation. The golden observer stack already owns the binary Parikh
matrix representation whose central doubled-Magnus entry is
`m = 2 P - r z`. The Weyl stack independently derives the phase `a*b*m` from
the literal wavefunction action.

This module only composes those owners. The represented universal primitive
logarithm has central entry `magnusCenter`; the concrete Weyl normal form is
rewritten through that coordinate. For one long-before-short pair, the
free-Lie bracket has central coefficient one and exponentiates to the physical
word/reversal phase `exp(i*2*a*b)`.

The older draft PR #4504 was audited first. Its relevant Fourier/free-Lie ideas
have since evolved into stronger current owners already present on this stack,
so no stale draft definition is copied here. No unbounded generator, completed
free Lie algebra or analytic BCH/Magnus convergence theorem is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.UniversalMagnusWeylPhaseBridge

open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.PrimitiveMagnusLog
open D5.S3.Observer.Chronology.StepTwoChronologicalSignature
open D5.S3.Observer.Chronology.StepTwoFreeLieBridge
open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra

noncomputable section

/-- Universal tensor signature of the canonical binary Parikh observation. -/
def binaryUniversalSignature (word : List Bool) : TensorSignature ℤ IntegerMatrix3 :=
  chronologicalTensorSignature ℤ IntegerMatrix3 binaryLetterObservation word

/-- The represented universal primitive logarithm has central entry equal to
the existing integer Magnus center. -/
theorem binary_universal_magnus_central_entry (word : List Bool) :
    (tensorMultiplication ℤ IntegerMatrix3
      (doubledPrimitiveMagnus ℤ IntegerMatrix3
        (binaryUniversalSignature word))) 0 2 = magnusCenter word := by
  rw [represent_doubled_primitive_magnus]
  change
    (doubledMagnusDegreeTwo
      (representTensorSignature ℤ IntegerMatrix3
        (binaryUniversalSignature word))) 0 2 = magnusCenter word
  rw [show
    representTensorSignature ℤ IntegerMatrix3 (binaryUniversalSignature word) =
      chronologicalSignature binaryLetterObservation word by
        unfold binaryUniversalSignature
        exact represent_chronological_tensor_signature
          ℤ IntegerMatrix3 binaryLetterObservation word]
  rw [binary_doubled_magnus_center, magnus_center_formula]

/-- Real scalar version of the universal central coordinate. -/
theorem binary_universal_magnus_central_entry_real (word : List Bool) :
    (((tensorMultiplication ℤ IntegerMatrix3
      (doubledPrimitiveMagnus ℤ IntegerMatrix3
        (binaryUniversalSignature word))) 0 2 : ℤ) : ℝ) =
      (magnusCenter word : ℝ) := by
  exact_mod_cast binary_universal_magnus_central_entry word

/-- The concrete Weyl normal form is controlled by the represented universal
primitive Magnus coordinate. -/
theorem run_word_normal_form_via_universal_magnus
    (a b : ℝ) (word : List Bool) (f : ℝ → ℂ) :
    runWord a b word f =
      Complex.exp ((((a * b *
        (((tensorMultiplication ℤ IntegerMatrix3
          (doubledPrimitiveMagnus ℤ IntegerMatrix3
            (binaryUniversalSignature word))) 0 2 : ℤ) : ℝ)) : ℝ) : ℂ) *
          Complex.I) •
        displacement (a * word.count true) (b * word.count false) f := by
  rw [binary_universal_magnus_central_entry_real]
  exact run_word_normal_form a b word f

/-- The universal free-Lie long-before-short bracket has unit central
coefficient in the canonical binary representation. -/
theorem binary_free_lie_true_false_central_entry :
    (freeLieEvaluation ℤ IntegerMatrix3 binaryLetterObservation
      ⁅FreeLieAlgebra.of ℤ true, FreeLieAlgebra.of ℤ false⁆) 0 2 = 1 := by
  have hFree := free_lie_evaluation_bracket
    ℤ IntegerMatrix3 binaryLetterObservation true false
  have hMagnus := doubled_magnus_two_events_eq_commutator
    binaryLetterObservation true false
  have hCenter := binary_doubled_magnus_center [true, false]
  calc
    (freeLieEvaluation ℤ IntegerMatrix3 binaryLetterObservation
        ⁅FreeLieAlgebra.of ℤ true, FreeLieAlgebra.of ℤ false⁆) 0 2 =
        commutator (binaryLetterObservation true)
          (binaryLetterObservation false) 0 2 := by
      exact congrArg (fun matrix => matrix 0 2) hFree
    _ = (doubledMagnusDegreeTwo
          (chronologicalSignature binaryLetterObservation [true, false])) 0 2 := by
      exact congrArg (fun matrix => matrix 0 2) hMagnus.symm
    _ = 1 := by
      simpa [scatteredTrueFalseCount] using hCenter

/-- The elementary free-Lie coefficient exponentiates to the concrete Weyl
word/reversal phase. -/
theorem two_letter_weyl_swap_phase_from_free_lie
    (a b : ℝ) (f : ℝ → ℂ) :
    runWord a b [true, false] f =
      Complex.exp ((((2 * a * b *
        (((freeLieEvaluation ℤ IntegerMatrix3 binaryLetterObservation
          ⁅FreeLieAlgebra.of ℤ true, FreeLieAlgebra.of ℤ false⁆) 0 2 : ℤ) : ℝ)) : ℝ) : ℂ) *
          Complex.I) •
        runWord a b [false, true] f := by
  rw [binary_free_lie_true_false_central_entry]
  simpa [magnus_center_formula, scatteredTrueFalseCount] using
    (word_reverse_relative_phase a b [true, false] f)

#print axioms binary_universal_magnus_central_entry
#print axioms binary_universal_magnus_central_entry_real
#print axioms run_word_normal_form_via_universal_magnus
#print axioms binary_free_lie_true_false_central_entry
#print axioms two_letter_weyl_swap_phase_from_free_lie

end
end D5.S3.Quantum.WeylChronology.UniversalMagnusWeylPhaseBridge
