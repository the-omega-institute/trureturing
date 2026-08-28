/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/DominanceEventAlgebraCharacterization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/DominanceEventAlgebraCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dominance is agreement on all observable events plus one separator. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality
import Mathlib.Algebra.Group.Indicator

/- Library-search audit trail (2026-08-27):
   * The current-tree exact primitive `observableEventAlgebra` supplies the
     source's fiber-constant event algebra and is imported rather than forked.
   * Current-tree searches for dominance together with universal observable
     event agreement and an existential separating event found no exact
     theorem on this carrier.
   * Pinned Mathlib supplies `Set.indicator`; no Mathlib theorem packages the
     source's kernel conjunction and both indicator clauses.
   * No new `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.DominanceEventAlgebraCharacterization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

universe u

/-- Complete dominance means that the homozygous and heterozygous states
agree on every observable event, while an observable event separates the
heterozygous state from the other homozygous state. -/
theorem complete_dominance_event_algebra_characterization
    {X O : Type u} (q : Concept X O) (xAA xAB xBB : X) :
    (Setoid.ker q xAA xAB ∧ ¬Setoid.ker q xAB xBB) ↔
      ((∀ event : Set X,
          event ∈ observableEventAlgebra q ->
            event.indicator (fun _ => (1 : Nat)) xAA =
              event.indicator (fun _ => (1 : Nat)) xAB) ∧
        ∃ event : Set X,
          event ∈ observableEventAlgebra q ∧
            event.indicator (fun _ => (1 : Nat)) xAB ≠
              event.indicator (fun _ => (1 : Nat)) xBB) := by
  constructor
  · rintro ⟨sameAAAB, differentABBB⟩
    constructor
    · intro event eventObservable
      have sameMembership := eventObservable sameAAAB
      by_cases aaIn : xAA ∈ event
      · have abIn : xAB ∈ event := sameMembership.mp aaIn
        simp [Set.indicator_of_mem, aaIn, abIn]
      · have abNotIn : xAB ∉ event := fun abIn =>
          aaIn (sameMembership.mpr abIn)
        simp [Set.indicator_of_notMem, aaIn, abNotIn]
    · let separatingEvent : Set X := {state | q state = q xAB}
      have separatingObservable :
          separatingEvent ∈ observableEventAlgebra q := by
        intro first second sameReadout
        change (q first = q xAB) ↔ q second = q xAB
        rw [sameReadout]
      have abIn : xAB ∈ separatingEvent := by
        change q xAB = q xAB
        rfl
      have bbNotIn : xBB ∉ separatingEvent := by
        intro bbIn
        change q xBB = q xAB at bbIn
        exact differentABBB bbIn.symm
      refine ⟨separatingEvent, separatingObservable, ?_⟩
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, abIn, bbNotIn]
  · rintro ⟨allEventsAgree, ⟨separatingEvent, separatingObservable,
      separatesABBB⟩⟩
    constructor
    · by_contra differentAAAB
      let aaFiber : Set X := {state | q state = q xAA}
      have aaFiberObservable : aaFiber ∈ observableEventAlgebra q := by
        intro first second sameReadout
        change (q first = q xAA) ↔ q second = q xAA
        rw [sameReadout]
      have indicatorAgreement := allEventsAgree aaFiber aaFiberObservable
      have aaIn : xAA ∈ aaFiber := by
        change q xAA = q xAA
        rfl
      have abNotIn : xAB ∉ aaFiber := by
        intro abIn
        change q xAB = q xAA at abIn
        exact differentAAAB abIn.symm
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, aaIn, abNotIn]
        at indicatorAgreement
    · intro sameABBB
      have sameMembership := separatingObservable sameABBB
      by_cases abIn : xAB ∈ separatingEvent
      · have bbIn : xBB ∈ separatingEvent := sameMembership.mp abIn
        exact separatesABBB (by
          simp [Set.indicator_of_mem, abIn, bbIn])
      · have bbNotIn : xBB ∉ separatingEvent := fun bbIn =>
          abIn (sameMembership.mpr bbIn)
        exact separatesABBB (by
          simp [Set.indicator_of_notMem, abIn, bbNotIn])

#print axioms complete_dominance_event_algebra_characterization

end D5.S3.ConceptDynamics.RefinementAlgebra.DominanceEventAlgebraCharacterization
