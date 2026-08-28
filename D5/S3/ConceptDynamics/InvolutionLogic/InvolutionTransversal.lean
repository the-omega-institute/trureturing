/- GID: D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A Boolean orientation of a fixed-point-free involution is an orbit transversal. -/

import D5.S3.ConceptDynamics.InvolutionLogic.AtomicNegationRigidity

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib supplies set image, preimage, complement, and involutions.
   * Repository searches found no accepted theorem identifying Boolean negation
     along an involution with a choice of one point from every two-cycle.
   * Atomic negation is reused from the companion rigidity module. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InvolutionLogic.InvolutionTransversal

open D5.S3.ConceptDynamics.InvolutionLogic.AtomicNegationRigidity

/-- `set` chooses exactly one side of every `involution` orbit. -/
def OrbitTransversal {X : Type*} (involution : X → X) (set : Set X) : Prop :=
  ∀ x, involution x ∈ set ↔ x ∉ set

/-- The transversal law is exactly a preimage-complement equation. -/
theorem orbitTransversal_iff_preimage_eq_compl
    {X : Type*} (involution : X → X) (set : Set X) :
    OrbitTransversal involution set ↔ involution ⁻¹' set = setᶜ := by
  constructor
  · intro transversal
    ext x
    exact transversal x
  · intro equality x
    have membership := Set.ext_iff.mp equality x
    exact membership

/-- Every orbit transversal forces the underlying transformation to be fixed-point free. -/
theorem fixedPointFree_of_orbitTransversal
    {X : Type*} {involution : X → X} {set : Set X}
    (transversal : OrbitTransversal involution set) :
    ∀ x, involution x ≠ x := by
  intro x fixed
  by_cases xInSet : x ∈ set
  · have xOutside : x ∉ set := by
      apply (transversal x).1
      simpa [fixed] using xInSet
    exact xOutside xInSet
  · have imageInSet : involution x ∈ set := (transversal x).2 xInSet
    exact xInSet (by simpa [fixed] using imageInSet)

/-- For an involution, the image of a transversal is its complement. -/
theorem image_eq_compl_of_orbitTransversal
    {X : Type*} {involution : X → X} {set : Set X}
    (involutive : Function.Involutive involution)
    (transversal : OrbitTransversal involution set) :
    involution '' set = setᶜ := by
  ext y
  constructor
  · rintro ⟨x, xInSet, rfl⟩
    change involution x ∉ set
    intro imageInSet
    exact (transversal x).1 imageInSet xInSet
  · intro yOutsideSet
    change y ∉ set at yOutsideSet
    refine ⟨involution y, (transversal y).2 yOutsideSet, ?_⟩
    exact involutive y

/-- Every singleton is a transversal in an atomic-negation universe. -/
theorem singleton_orbitTransversal_of_atomicNegation
    {X : Type*} (negation : AtomicNegation X) (x : X) :
    OrbitTransversal negation.neg ({x} : Set X) := by
  intro y
  change negation.neg y = x ↔ y ≠ x
  constructor
  · intro imageEquals same
    subst y
    exact negation.neg_ne x imageEquals
  · intro different
    have yIsOther : y = negation.neg x :=
      (negation.other_iff x y).1 different
    rw [yIsOther, negation.involutive x]

/-- An involution for which every singleton is a transversal is an atomic negation. -/
def atomicNegationOfSingletonTransversals
    {X : Type*} (involution : X → X)
    (involutive : Function.Involutive involution)
    (singletons : ∀ x, OrbitTransversal involution ({x} : Set X)) :
    AtomicNegation X where
  neg := involution
  other_iff x y := by
    constructor
    · intro different
      have imageEquals : involution y = x := (singletons x y).2 different
      calc
        y = involution (involution y) := (involutive y).symm
        _ = involution x := congrArg involution imageEquals
    · intro equality same
      apply fixedPointFree_of_orbitTransversal (singletons x) x
      calc
        involution x = y := equality.symm
        _ = x := same

#print axioms orbitTransversal_iff_preimage_eq_compl
#print axioms image_eq_compl_of_orbitTransversal
#print axioms atomicNegationOfSingletonTransversals

end D5.S3.ConceptDynamics.InvolutionLogic.InvolutionTransversal
