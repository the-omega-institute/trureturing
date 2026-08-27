/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/EventSeparationCharacterization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/EventSeparationCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Readout fibers are exactly the pairs agreeing on every observable event. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

/- Library-search audit trail (2026-08-27):
   * Exact current-tree hit `observableEventAlgebra` is the source's
     fiber-constant event algebra and is imported rather than redeclared.
   * `observable_event_algebra_duality` characterizes inclusion between two
     whole kernels; it does not state this pointwise separation theorem.
   * Current-tree and pinned-Mathlib shape searches found no exact theorem
     equating one kernel pair with agreement on all of these events.
   * No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.EventSeparationCharacterization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

universe u

/-- Two states share a readout fiber exactly when every event observable
through that readout gives them the same membership value. -/
theorem event_separation_characterization
    {X O : Type u} (q : Concept X O) (x y : X) :
    Setoid.ker q x y <->
      forall event : Set X,
        event ∈ observableEventAlgebra q -> (x ∈ event <-> y ∈ event) := by
  constructor
  · intro sameReadout event eventObservable
    exact eventObservable sameReadout
  · intro allEventsAgree
    let fiber : Set X := {state | q state = q x}
    have fiberObservable : fiber ∈ observableEventAlgebra q := by
      intro first second sameReadout
      change (q first = q x) <-> q second = q x
      rw [sameReadout]
    have sameMembership := allEventsAgree fiber fiberObservable
    have xInFiber : x ∈ fiber := by
      change q x = q x
      rfl
    have yInFiber := sameMembership.mp xInFiber
    change q x = q y
    exact yInFiber.symm

#print axioms event_separation_characterization

end D5.S3.ConceptDynamics.RefinementAlgebra.EventSeparationCharacterization
