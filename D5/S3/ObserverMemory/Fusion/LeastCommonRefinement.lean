/- GID: D5/S3/ObserverMemory/Fusion/LeastCommonRefinement
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/LeastCommonRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize the least common quotient refinement by its unique surjective factor. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-17):
   * Repository and pinned-Mathlib searches found no exact two-setoid common
     refinement theorem with existence, surjectivity, compatibility, and uniqueness.
   * Exact pinned-Mathlib hit: `Function.rightInverse_surjInv` supplies the
     representative of each value of an arbitrary surjection and is applied below.
   * Adjacent repository quotient-factorization theorems have either a quotient
     source or additional dynamics and therefore do not subsume this statement.
-/

namespace D5.S3.ObserverMemory.Fusion.LeastCommonRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A completion mapping surjectively and compatibly to two quotient completions
maps uniquely and surjectively to the quotient by the intersection relation. -/
theorem least_common_refinement_universal_property
    {Y W : Type*} (first second : Setoid Y)
    (projection : Y -> W)
    (toFirst : W -> Quotient first) (toSecond : W -> Quotient second)
    (projectionSurjective : Function.Surjective projection)
    (_firstSurjective : Function.Surjective toFirst)
    (_secondSurjective : Function.Surjective toSecond)
    (firstCompatible : forall y,
      toFirst (projection y) = (Quotient.mk'' y : Quotient first))
    (secondCompatible : forall y,
      toSecond (projection y) = (Quotient.mk'' y : Quotient second)) :
    ExistsUnique fun descend : W -> Quotient (first ⊓ second) =>
      Function.Surjective descend ∧
        forall y, descend (projection y) = Quotient.mk'' y := by
  apply Eq.mp (propext (Iff.refl _))
  have kernelRefines : Setoid.ker projection ≤ first ⊓ second := by
    intro y y' hyy'
    constructor
    · apply Quotient.exact
      calc
        (Quotient.mk'' y : Quotient first) = toFirst (projection y) :=
          (firstCompatible y).symm
        _ = toFirst (projection y') := congrArg toFirst hyy'
        _ = Quotient.mk'' y' := firstCompatible y'
    · apply Quotient.exact
      calc
        (Quotient.mk'' y : Quotient second) = toSecond (projection y) :=
          (secondCompatible y).symm
        _ = toSecond (projection y') := congrArg toSecond hyy'
        _ = Quotient.mk'' y' := secondCompatible y'
  let representative : W -> Y := Function.surjInv projectionSurjective
  have representativeRight : Function.RightInverse representative projection :=
    Function.rightInverse_surjInv projectionSurjective
  let descend : W -> Quotient (first ⊓ second) :=
    fun w => Quotient.mk'' (representative w)
  have projectionFactors (y : Y) :
      descend (projection y) = Quotient.mk'' y := by
    apply Quotient.sound'
    exact kernelRefines (representativeRight (projection y))
  have descendSurjective : Function.Surjective descend := by
    intro fused
    refine Quotient.inductionOn' fused fun y => ?_
    exact ⟨projection y, projectionFactors y⟩
  refine ⟨descend, ⟨descendSurjective, projectionFactors⟩, ?_⟩
  intro candidate hCandidate
  funext w
  rcases projectionSurjective w with ⟨y, rfl⟩
  exact (hCandidate.2 y).trans (projectionFactors y).symm

example : Nonempty Unit := ⟨()⟩

example :
    ExistsUnique fun descend :
        Unit -> Quotient ((⊥ : Setoid Unit) ⊓ (⊥ : Setoid Unit)) =>
      Function.Surjective descend ∧
        forall y, descend ((id : Unit -> Unit) y) = Quotient.mk'' y := by
  apply least_common_refinement_universal_property
      (first := (⊥ : Setoid Unit))
      (second := (⊥ : Setoid Unit))
      (projection := id)
      (toFirst := fun y => Quotient.mk'' y)
      (toSecond := fun y => Quotient.mk'' y)
  · exact Function.surjective_id
  · exact Quotient.mk_surjective
  · exact Quotient.mk_surjective
  · intro y
    rfl
  · intro y
    rfl

#print axioms least_common_refinement_universal_property

end D5.S3.ObserverMemory.Fusion.LeastCommonRefinement
