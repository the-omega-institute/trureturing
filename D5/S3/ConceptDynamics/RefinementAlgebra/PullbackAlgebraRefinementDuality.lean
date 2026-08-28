/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/PullbackAlgebraRefinementDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realized-image refinement is dual to kernels and the canonical pullback algebra. -/

import D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-26):
   * Body-shape search `{observable | Function.FactorsThrough observable q}`
     found the canonical `PullbackAlgebra` owner in
     `Dialectics.DeterministicInterfaceEquivalence`; it is imported directly.
   * `ConceptJoinUniversal.Refines` and
     `ConceptKernelOrderDuality.effective_refines_iff_reverse_kernel` are the
     current-tree refinement and kernel owners and are reused below.
   * Current-tree and pinned-Mathlib searches for `FactorsThrough` with kernel
     inclusion found no theorem packaging all three source equivalences.
     Mathlib's general `Function.FactorsThrough` API is used through the owner. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraRefinementDuality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- On realized images, refinement, reverse kernel inclusion, and inclusion of
the canonical pullback algebras are equivalent. -/
theorem pullback_algebra_refinement_duality
    {X O P : Type u} (q : Concept X O) (r : Concept X P) :
    (Refines (Set.rangeFactorization q) (Set.rangeFactorization r) <->
      Setoid.ker r <= Setoid.ker q) /\
    (Setoid.ker r <= Setoid.ker q <->
      PullbackAlgebra q ⊆ PullbackAlgebra r) := by
  let qEffective : EffectiveConcept X := {
    Coordinate := Set.range q
    readout := Set.rangeFactorization q
    effective := Set.rangeFactorization_surjective }
  let rEffective : EffectiveConcept X := {
    Coordinate := Set.range r
    readout := Set.rangeFactorization r
    effective := Set.rangeFactorization_surjective }
  have qKernel : Setoid.ker (Set.rangeFactorization q) = Setoid.ker q := by
    ext x y
    exact Set.rangeFactorization_eq_rangeFactorization_iff x y
  have rKernel : Setoid.ker (Set.rangeFactorization r) = Setoid.ker r := by
    ext x y
    exact Set.rangeFactorization_eq_rangeFactorization_iff x y
  have refinementKernel :
      Refines (Set.rangeFactorization q) (Set.rangeFactorization r) <->
        Setoid.ker r <= Setoid.ker q := by
    have canonical := effective_refines_iff_reverse_kernel qEffective rEffective
    rw [← qKernel, ← rKernel]
    simpa only [qEffective, rEffective] using canonical
  refine ⟨refinementKernel, ?_⟩
  constructor
  · intro kernelInclusion observable observableThroughQ x y sameR
    exact observableThroughQ (kernelInclusion sameR)
  · intro algebraInclusion x y sameR
    let distinguishingObservable : X -> Prop := fun state => q state = q x
    have observableThroughQ : distinguishingObservable ∈ PullbackAlgebra q := by
      change Function.FactorsThrough distinguishingObservable q
      intro a b sameQ
      apply propext
      change (q a = q x) <-> q b = q x
      rw [sameQ]
    have observableThroughR := algebraInclusion observableThroughQ
    have sameTruthValue := observableThroughR sameR
    change (q x = q x) = (q y = q x) at sameTruthValue
    exact (Eq.mp sameTruthValue rfl).symm

#print axioms pullback_algebra_refinement_duality

end D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraRefinementDuality
