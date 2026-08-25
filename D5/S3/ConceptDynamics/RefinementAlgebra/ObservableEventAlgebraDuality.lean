/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Realized-image refinement is dual to kernels and observable event algebras. -/

import D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality
import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-25):
   * Exact current-tree hits `ConceptJoinUniversal.Refines` and
     `ConceptKernelOrderDuality.effective_refines_iff_reverse_kernel` supply the
     canonical refinement relation and its reverse-kernel characterization.
   * Body-shape searches found `QuestionAlgebraDuality.AnswerableQuestions` on
     Boolean-valued functions, but no event algebra on the source's exact
     `Set X` carrier. The definition below therefore uses the source's stated
     fiber-constancy predicate directly rather than forking the Boolean carrier.
   * Exact pinned-Mathlib hits `Set.rangeFactorization`, its surjectivity theorem,
     and its equality API supply the effective carrier and kernel bridge.
   * Repository and pinned-Mathlib searches found no theorem packaging the
     refinement, kernel, and observable-event-algebra equivalences together. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.ConceptKernelOrderDuality

universe u

/-- Events observable through a readout have membership constant on every
readout fiber. -/
def observableEventAlgebra {X O : Type u} (q : Concept X O) : Set (Set X) :=
  {event | ∀ ⦃x y : X⦄, q x = q y → (x ∈ event ↔ y ∈ event)}

/-- On realized images, refinement, reverse kernel inclusion, and inclusion of
observable event algebras are equivalent. -/
theorem observable_event_algebra_duality
    {X O Q : Type u} (q : Concept X O) (r : Concept X Q) :
    (Refines (Set.rangeFactorization q) (Set.rangeFactorization r) ↔
      Setoid.ker r ≤ Setoid.ker q) ∧
    (Setoid.ker r ≤ Setoid.ker q ↔
      observableEventAlgebra q ⊆ observableEventAlgebra r) := by
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
      Refines (Set.rangeFactorization q) (Set.rangeFactorization r) ↔
        Setoid.ker r ≤ Setoid.ker q := by
    have canonical := effective_refines_iff_reverse_kernel qEffective rEffective
    rw [← qKernel, ← rKernel]
    simpa only [qEffective, rEffective] using canonical
  refine ⟨refinementKernel, ?_⟩
  constructor
  · intro kernelInclusion event observedByQ x y sameR
    exact observedByQ (kernelInclusion sameR)
  · intro algebraInclusion x y sameR
    let distinguishingEvent : Set X :=
      {state | q state = q x}
    have observedByQ : distinguishingEvent ∈ observableEventAlgebra q := by
      intro a b sameQ
      change (q a = q x) ↔ q b = q x
      rw [sameQ]
    have observedByR := algebraInclusion observedByQ
    have sameMembership := observedByR sameR
    have sameQ : q y = q x := by
      exact sameMembership.mp (by simp [distinguishingEvent])
    change q x = q y
    exact sameQ.symm

#print axioms observable_event_algebra_duality

end D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality
