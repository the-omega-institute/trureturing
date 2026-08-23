/- GID: D5/S3/Quantum/Sharpness/SideFlipPositivityRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Sharpness/SideFlipPositivityRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A side-flip-invariant nonnegative subspace is isotropic for the swap form. -/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/- Library-search audit trail (2026-08-23):
   * Repository searches for the side-flip, coordinate-swap form, and positivity rigidity found no
     equivalent declaration. The existing branch-vector Hermitian product does not define either
     of the source's canonical coordinate operators.
   * Pinned-Mathlib searches found no exact theorem for side-flip-invariant nonnegative subspaces.
     The proof uses only the order consequence of the explicit sign-flip computation. -/

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Sharpness.SideFlipPositivityRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The side operator on the two complex evaluation coordinates. -/
def sideFlip (v : Fin 2 -> Complex) : Fin 2 -> Complex :=
  ![v 0, -v 1]

/-- Reflection exchanges the right and left evaluation coordinates. -/
def reflectionSwap (v : Fin 2 -> Complex) : Fin 2 -> Complex :=
  ![v 1, v 0]

/-- The real Hermitian quadratic form induced by coordinate reflection. -/
def reflectionForm (v : Fin 2 -> Complex) : Real :=
  Complex.re (∑ i, star (v i) * reflectionSwap v i)

theorem reflectionForm_sideFlip (v : Fin 2 -> Complex) :
    reflectionForm (sideFlip v) = -reflectionForm v := by
  simp [reflectionForm, reflectionSwap, sideFlip, Fin.sum_univ_two]
  ring

/-- A complex subspace invariant under the side operator cannot carry a strictly positive
direction of the reflection form when that form is nonnegative throughout the subspace. -/
theorem side_flip_positive_rigidity
    (W : Submodule Complex (Fin 2 -> Complex))
    (hInvariant : forall v, v ∈ W -> sideFlip v ∈ W)
    (hNonnegative : forall v, v ∈ W -> 0 <= reflectionForm v) :
    forall v, v ∈ W -> reflectionForm v = 0 := by
  intro v hv
  have hpos : 0 <= reflectionForm v := hNonnegative v hv
  have hneg : 0 <= -reflectionForm v := by
    rw [← reflectionForm_sideFlip]
    exact hNonnegative (sideFlip v) (hInvariant v hv)
  linarith

#print axioms side_flip_positive_rigidity

end D5.S3.Quantum.Sharpness.SideFlipPositivityRigidity
