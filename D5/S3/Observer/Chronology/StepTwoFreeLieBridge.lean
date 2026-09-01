/- GID: D5/S3/Observer/Chronology/StepTwoFreeLieBridge
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/StepTwoFreeLieBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two-event primitive tensor logarithm evaluates to the degree-two free-Lie bracket in every associative ring representation. -/

import D5.S3.Observer.Chronology.PrimitiveMagnusLog
import Mathlib.Algebra.Lie.Free
import Mathlib.Tactic

/-!
# Step-two free-Lie bridge

The universal free Lie algebra on event labels contains the bracket of two
formal events. Any observation of those labels in an associative ring extends
uniquely to a Lie morphism. At degree two, evaluating the free-Lie bracket is
identical to multiplying the antisymmetric primitive tensor

`x ⊗ y - y ⊗ x`.

Consequently the doubled primitive Magnus coordinate of a two-event
chronology is exactly the represented free-Lie bracket. This is a finite
universal-property bridge. It does not construct a completed free Lie
algebra, a full logarithmic signature, PBW filtrations, or analytic Magnus
convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped TensorProduct

namespace D5.S3.Observer.Chronology.StepTwoFreeLieBridge

open D5.S3.Observer.Chronology.TruncatedTensorSignature
open D5.S3.Observer.Chronology.PrimitiveMagnusLog

universe u v

/-- The formal degree-two free-Lie bracket of two event labels. -/
def freeLieDegreeTwo
    {Event : Type u} (first second : Event) :
    FreeLieAlgebra ℤ Event :=
  ⁅FreeLieAlgebra.of ℤ Event first,
    FreeLieAlgebra.of ℤ Event second⁆

/-- Universal evaluation of formal event Lie words in an associative ring. -/
def freeLieEvaluation
    {Event : Type u} {A : Type v} [Ring A]
    (observe : Event → A) :
    FreeLieAlgebra ℤ Event →ₗ⁅ℤ⁆ A :=
  FreeLieAlgebra.lift ℤ Event A observe

/-- Multiplication contracts an integral tensor of ring elements. -/
def tensorMultiply
    {A : Type v} [Ring A] :
    TensorProduct ℤ A A →ₗ[ℤ] A :=
  Algebra.TensorProduct.mul ℤ A

@[simp]
theorem tensorMultiply_tmul
    {A : Type v} [Ring A] (x y : A) :
    tensorMultiply (x ⊗ₜ[ℤ] y) = x * y := by
  rfl

/-- Evaluation of the formal free-Lie bracket is the ring commutator. -/
theorem freeLieEvaluation_degreeTwo
    {Event : Type u} {A : Type v} [Ring A]
    (observe : Event → A) (first second : Event) :
    freeLieEvaluation observe (freeLieDegreeTwo first second) =
      observe first * observe second -
        observe second * observe first := by
  simp [freeLieEvaluation, freeLieDegreeTwo, lie_bracket]

/-- Tensor multiplication sends the antisymmetric tensor bracket to the ring
commutator. -/
theorem tensorMultiply_tensorCommutator
    {A : Type v} [Ring A] (x y : A) :
    tensorMultiply (tensorCommutator (R := ℤ) x y) =
      x * y - y * x := by
  simp [tensorMultiply, tensorCommutator]

/-- The tensor primitive and the free-Lie bracket have the same value in every
associative ring representation. -/
theorem tensor_primitive_eq_freeLie_evaluation
    {Event : Type u} {A : Type v} [Ring A]
    (observe : Event → A) (first second : Event) :
    tensorMultiply
        (tensorCommutator (R := ℤ)
          (observe first) (observe second)) =
      freeLieEvaluation observe (freeLieDegreeTwo first second) := by
  rw [tensorMultiply_tensorCommutator,
    freeLieEvaluation_degreeTwo]

/-- The represented doubled primitive Magnus coordinate of a two-event word
is exactly its degree-two free-Lie bracket. -/
theorem chronological_primitive_eq_freeLie_evaluation
    {Event : Type u} {A : Type v} [Ring A]
    (observe : Event → A) (first second : Event) :
    tensorMultiply
        (doubledPrimitiveMagnus
          (chronologicalTensorSignature (R := ℤ) observe
            [first, second])) =
      freeLieEvaluation observe (freeLieDegreeTwo first second) := by
  rw [doubledPrimitiveMagnus_two_events]
  exact tensor_primitive_eq_freeLie_evaluation
    observe first second

/-- Reversing two labels negates the represented free-Lie bracket. -/
theorem freeLieEvaluation_degreeTwo_swap
    {Event : Type u} {A : Type v} [Ring A]
    (observe : Event → A) (first second : Event) :
    freeLieEvaluation observe (freeLieDegreeTwo second first) =
      -freeLieEvaluation observe (freeLieDegreeTwo first second) := by
  simp [freeLieEvaluation_degreeTwo]

example :
    freeLieEvaluation (fun value : ℤ => value)
        (freeLieDegreeTwo 1 2) = 0 := by
  norm_num [freeLieEvaluation_degreeTwo]

#print axioms freeLieEvaluation_degreeTwo
#print axioms tensorMultiply_tensorCommutator
#print axioms tensor_primitive_eq_freeLie_evaluation
#print axioms chronological_primitive_eq_freeLie_evaluation
#print axioms freeLieEvaluation_degreeTwo_swap

end D5.S3.Observer.Chronology.StepTwoFreeLieBridge
