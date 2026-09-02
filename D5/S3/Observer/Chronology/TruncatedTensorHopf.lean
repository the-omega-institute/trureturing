/- GID: D5/S3/Observer/Chronology/TruncatedTensorHopf
   generality: G
   mirror-B: D5/B/S3/Observer/Chronology/TruncatedTensorHopf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Degree-two tensor signatures satisfy the truncated group-like balance. -/

import D5.S3.Observer.Chronology.TruncatedTensorSignature
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Truncated tensor Hopf balance

The universal chronological signature through tensor degree two already has
its Chen multiplication. This module supplies the degree-two shadow of the
standard tensor-Hopf group-like equation. The tensor flip is Mathlib's
canonical symmetry of `V ⊗[R] V`, and a doubled step-two signature `(x,D)` is
group-like exactly when

`D + flip D = 2 • (x ⊗ₜ x)`.

Single-event signatures satisfy this equation. The equation is preserved by
chronological multiplication, so every finite chronological word is
step-two group-like.

This file deliberately reuses the existing tensor-square signature and
Mathlib tensor symmetry. It does not define a parallel tensor product. It also
does not yet construct the full tensor algebra, install a `Bialgebra` or
`HopfAlgebra` instance, define an infinite signature, or prove convergence of
a tensor series. Those stronger structures require all tensor degrees or an
explicit truncated graded algebra with its full linear coproduct.
-/

/- Library-search audit trail (2026-09-01):
   * `TruncatedTensorSignature` owns the universal degree-one and doubled
     degree-two chronological coordinates and their Chen multiplication.
   * Pinned Mathlib's `TensorProduct.comm` is the canonical tensor-factor
     symmetry and supplies its linearity and pure-tensor computation rules.
   * Pinned Mathlib also contains the standard `Bialgebra`, `HopfAlgebra`,
     `IsGroupLikeElem`, antipode, convolution, and primitive-element APIs.
     The present theorem is the exact degree-two balance that a later graded
     realization must transport into those standard interfaces.
   * Repository search found no owner of this tensor-square group-like balance
     or its closure under chronological multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open TensorProduct

namespace D5.S3.Observer.Chronology.TruncatedTensorHopf

open D5.S3.Observer.Chronology.TruncatedTensorSignature

universe u v w

variable (R : Type u) (V : Type v)
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

/-- The canonical interchange of the two degree-one tensor factors. -/
def tensorFlip : V ⊗[R] V ≃ₗ[R] V ⊗[R] V :=
  TensorProduct.comm R V V

@[simp]
theorem tensor_flip_tmul (left right : V) :
    tensorFlip R V (left ⊗ₜ[R] right) = right ⊗ₜ[R] left := by
  rfl

/-- The degree-two group-like equation in doubled coordinates. -/
def IsStepTwoGroupLike
    (signature : TensorSignature R V) : Prop :=
  signature.doubledDegreeTwo +
      tensorFlip R V signature.doubledDegreeTwo =
    2 • (signature.degreeOne ⊗ₜ[R] signature.degreeOne)

/-- The empty chronological signature is group-like. -/
theorem identity_is_step_two_group_like :
    IsStepTwoGroupLike R V (1 : TensorSignature R V) := by
  simp [IsStepTwoGroupLike, TensorSignature.identity, tensorFlip]

/-- A single-event truncated exponential is group-like through degree two. -/
theorem event_tensor_signature_is_step_two_group_like
    (value : V) :
    IsStepTwoGroupLike R V (eventTensorSignature R V value) := by
  unfold IsStepTwoGroupLike eventTensorSignature tensorFlip
  simp [two_nsmul]

/-- The degree-two group-like equation is closed under Chen multiplication. -/
theorem step_two_group_like_mul
    (left right : TensorSignature R V)
    (leftGroupLike : IsStepTwoGroupLike R V left)
    (rightGroupLike : IsStepTwoGroupLike R V right) :
    IsStepTwoGroupLike R V (left * right) := by
  rcases left with ⟨leftOne, leftTwo⟩
  rcases right with ⟨rightOne, rightTwo⟩
  change
    leftTwo + tensorFlip R V leftTwo =
      2 • (leftOne ⊗ₜ[R] leftOne) at leftGroupLike
  change
    rightTwo + tensorFlip R V rightTwo =
      2 • (rightOne ⊗ₜ[R] rightOne) at rightGroupLike
  change
    (leftTwo + 2 • (leftOne ⊗ₜ[R] rightOne) + rightTwo) +
        tensorFlip R V
          (leftTwo + 2 • (leftOne ⊗ₜ[R] rightOne) + rightTwo) =
      2 • ((leftOne + rightOne) ⊗ₜ[R] (leftOne + rightOne))
  rw [map_add, map_add, map_nsmul, tensor_flip_tmul]
  calc
    _ =
        (leftTwo + tensorFlip R V leftTwo) +
          (rightTwo + tensorFlip R V rightTwo) +
          2 • (leftOne ⊗ₜ[R] rightOne) +
          2 • (rightOne ⊗ₜ[R] leftOne) := by
      abel
    _ =
        2 • (leftOne ⊗ₜ[R] leftOne) +
          2 • (rightOne ⊗ₜ[R] rightOne) +
          2 • (leftOne ⊗ₜ[R] rightOne) +
          2 • (rightOne ⊗ₜ[R] leftOne) := by
      rw [leftGroupLike, rightGroupLike]
    _ =
        2 • ((leftOne + rightOne) ⊗ₜ[R]
          (leftOne + rightOne)) := by
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
        nsmul_add]
      abel

/-- Every finite chronological tensor signature is group-like through degree
two. -/
theorem chronological_tensor_signature_is_step_two_group_like
    {Event : Type w} (observe : Event → V) (events : List Event) :
    IsStepTwoGroupLike R V
      (chronologicalTensorSignature R V observe events) := by
  induction events with
  | nil =>
      exact identity_is_step_two_group_like R V
  | cons event events inductionHypothesis =>
      rw [chronological_tensor_signature_cons]
      exact step_two_group_like_mul R V _ _
        (event_tensor_signature_is_step_two_group_like R V (observe event))
        inductionHypothesis

#print axioms tensor_flip_tmul
#print axioms identity_is_step_two_group_like
#print axioms event_tensor_signature_is_step_two_group_like
#print axioms step_two_group_like_mul
#print axioms chronological_tensor_signature_is_step_two_group_like

end D5.S3.Observer.Chronology.TruncatedTensorHopf
