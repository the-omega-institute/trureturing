/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventComplementPersistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/ObservableEventComplementPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complementing a fiber-constant event preserves every residual equivalence. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

/- Library-search audit trail (2026-08-27):
   * Body-shape and exact-name searches found the canonical source predicate
     `ObservableEventAlgebraDuality.observableEventAlgebra`; it is imported
     rather than redeclared.
   * Current-tree searches for observable-event complement closure and for the
     two simultaneous membership equivalences found no matching declaration.
   * Pinned Mathlib supplies `Set.mem_compl_iff` and ordinary propositional
     negation congruence, but no theorem on the repository's exact observable
     event carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventComplementPersistence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

universe u

/-- An observable event and its complement are both constant on a readout
fiber, so Boolean negation cannot separate two residual-equivalent states. -/
theorem observable_event_complement_persistence
    {X O : Type u} (q : Concept X O) (event : Set X) (x y : X)
    (eventObservable : event ∈ observableEventAlgebra q)
    (sameResidual : Setoid.ker q x y) :
    eventᶜ ∈ observableEventAlgebra q /\
      (x ∈ event <-> y ∈ event) /\
      (x ∈ eventᶜ <-> y ∈ eventᶜ) := by
  have sameEvent : x ∈ event <-> y ∈ event := eventObservable sameResidual
  have complementObservable : eventᶜ ∈ observableEventAlgebra q := by
    intro first second sameFiber
    change (first ∉ event) <-> second ∉ event
    exact not_congr (eventObservable sameFiber)
  refine ⟨complementObservable, sameEvent, ?_⟩
  change (x ∉ event) <-> y ∉ event
  exact not_congr sameEvent

#print axioms observable_event_complement_persistence

end D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventComplementPersistence
