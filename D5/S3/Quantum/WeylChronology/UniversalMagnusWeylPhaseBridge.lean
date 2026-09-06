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

This module closes the representation gap between two already-owned layers.
The chronology library has a universal step-two tensor signature, its primitive
Magnus logarithm, a represented associative-algebra shadow, and a free-Lie
interpretation.  The golden observer stack has the standard binary Parikh
matrix representation whose central doubled-Magnus entry is the integer
`m = 2 P - r z`.  The Weyl stack independently proved from the literal
wavefunction action that exactly the same integer multiplies the geometric
phase `a*b*m`.

No second Magnus coordinate is introduced here.  The first theorem transports
the universal primitive tensor logarithm through the repository's existing
`tensorMultiplication` representation and identifies its `(0,2)` entry with
the existing `magnusCenter`.  The Weyl normal form is then rewritten through
that universal coordinate.  For the elementary long-before-short pair, the
existing free-Lie evaluation has central entry one, and the physical swap
phase is exactly `exp(i*2*a*b)` times that free-Lie coefficient.

The operational word executor is an anti-representation of chronological list
order: the list head acts first, hence later operators multiply on the left.
The factor two in the two-letter swap is therefore the group-commutator phase;
the single compensated history retains the half phase `a*b*m`.

The older draft PR #4504 was audited before this file was written.  Its
Fourier/free-Lie ideas have since evolved into the stronger current owners
`StepTwoFreeLieBridge` and `FiniteFourierMagnusCommutator`, both already present
on this stack.  This module consumes the current owners rather than copying the
stale draft definitions.
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

noncomputable section

/-- The universal tensor signature of the canonical binary Parikh observation. -/
def binaryUniversalSignature (word : List Bool) :
    TensorSignature ℤ IntegerMatrix3 :=
  chronologicalTensorSignature ℤ IntegerMatrix3 binaryLetterObservation word

/-- The central entry of the represented universal primitive logarithm is
exactly the existing integer Magnus center.  This is the representation bridge
from the tensor-level chronology to the binary observer used by the Weyl lane. -/
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

/-- The same bridge after casting the central integer coordinate to the real
scalar used by the continuous Weyl representation. -/
theorem binary_universal_magnus_central_entry_real (word : List Bool) :
    (((tensorMultiplication ℤ IntegerMatrix3
      (doubledPrimitiveMagnus ℤ IntegerMatrix3
        (binaryUniversalSignature word))) 0 2 : ℤ) : ℝ) =
      (magnusCenter word : ℝ) := by
  exact_mod_cast binary_universal_magnus_central_entry word

/-- The concrete Weyl normal form is controlled by the represented universal
primitive Magnus coordinate, rather than by a separately introduced phase
counter. -/
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

/-- The universal free-Lie bracket of long followed by short has unit central
coefficient in the canonical binary Parikh representation. -/
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

/-- For the elementary ordered pair, the physical Weyl swap phase is exactly
twice `a*b` times the central coefficient of the universal free-Lie bracket.
This is the finite free-Lie-to-Weyl representation statement; it does not use
infinitesimal unbounded generators or a BCH convergence theorem. -/
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
