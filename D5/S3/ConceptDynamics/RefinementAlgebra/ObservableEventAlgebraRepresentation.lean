/- GID: D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fiber-constant events are canonically the powerset of the realized readout range. -/

import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality
import Mathlib.Order.BooleanSubalgebra

/- Library-search audit trail (2026-08-26):
   * Exact current-tree hit `observableEventAlgebra` is the source's
     fiber-constant event predicate and is imported rather than redeclared.
   * Repository body-shape searches for image/preimage maps involving
     `Set.rangeFactorization q` found no existing observable-event
     representation or Boolean-subalgebra wrapper.
   * Pinned Mathlib has no exact representation theorem. Exact components
     `BooleanSubalgebra`, `Set.rangeFactorization_surjective`, and
     `Set.image_preimage_eq` are applied below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraRepresentation

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraDuality

universe u

/-- The existing fiber-constant event predicate, bundled with its inherited
Boolean operations on subsets of the state carrier. -/
def observableEventBooleanAlgebra {X O : Type u} (q : Concept X O) :
    BooleanSubalgebra (Set X) where
  carrier := observableEventAlgebra q
  supClosed' := by
    intro left leftObservable right rightObservable x y sameReadout
    constructor
    · intro membership
      rcases membership with leftMembership | rightMembership
      · exact Or.inl ((leftObservable sameReadout).mp leftMembership)
      · exact Or.inr ((rightObservable sameReadout).mp rightMembership)
    · intro membership
      rcases membership with leftMembership | rightMembership
      · exact Or.inl ((leftObservable sameReadout).mpr leftMembership)
      · exact Or.inr ((rightObservable sameReadout).mpr rightMembership)
  infClosed' := by
    intro left leftObservable right rightObservable x y sameReadout
    constructor
    · rintro ⟨leftMembership, rightMembership⟩
      exact ⟨(leftObservable sameReadout).mp leftMembership,
        (rightObservable sameReadout).mp rightMembership⟩
    · rintro ⟨leftMembership, rightMembership⟩
      exact ⟨(leftObservable sameReadout).mpr leftMembership,
        (rightObservable sameReadout).mpr rightMembership⟩
  compl_mem' := by
    intro event eventObservable x y sameReadout
    exact not_congr (eventObservable sameReadout)
  bot_mem' := by
    intro x y _
    rfl

/-- Send a fiber-constant event to the set of realized readout values met by
that event. Its inverse pulls a set of realized values back along the canonical
range factorization. -/
def observableEventRepresentation {X O : Type u} (q : Concept X O) :
    observableEventBooleanAlgebra q ≃o Set (Set.range q) where
  toFun event := Set.rangeFactorization q '' (event : Set X)
  invFun observed :=
    ⟨Set.rangeFactorization q ⁻¹' observed, by
      intro x y sameReadout
      have sameEffectiveReadout :
          Set.rangeFactorization q x = Set.rangeFactorization q y :=
        Subtype.ext sameReadout
      change Set.rangeFactorization q x ∈ observed ↔
        Set.rangeFactorization q y ∈ observed
      rw [sameEffectiveReadout]⟩
  left_inv event := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨y, yInEvent, sameEffectiveReadout⟩
      have sameReadout : q y = q x :=
        congrArg Subtype.val sameEffectiveReadout
      exact (event.property sameReadout).mp yInEvent
    · intro xInEvent
      exact ⟨x, xInEvent, rfl⟩
  right_inv observed :=
    Set.image_preimage_eq observed Set.rangeFactorization_surjective
  map_rel_iff' := by
    intro left right
    constructor
    · intro imageInclusion x xInLeft
      have effectiveInLeft :
          Set.rangeFactorization q x ∈
            Set.rangeFactorization q '' (left : Set X) :=
        ⟨x, xInLeft, rfl⟩
      obtain ⟨y, yInRight, sameEffectiveReadout⟩ :=
        imageInclusion effectiveInLeft
      have sameReadout : q y = q x :=
        congrArg Subtype.val sameEffectiveReadout
      exact (right.property sameReadout).mp yInRight
    · intro eventInclusion observed observedInLeft
      obtain ⟨x, xInLeft, rfl⟩ := observedInLeft
      exact ⟨x, eventInclusion xInLeft, rfl⟩

/-- The observable-event Boolean algebra is canonically isomorphic to the
powerset of the effective output. The public computation rule uniquely fixes
the isomorphism as image under the realized-range projection. -/
theorem observable_event_algebra_representation
    {X O : Type u} (q : Concept X O) :
    ∃! representation :
        observableEventBooleanAlgebra q ≃o Set (Set.range q),
      ∀ event,
        representation event =
          Set.rangeFactorization q '' (event : Set X) := by
  refine ⟨observableEventRepresentation q, fun _ => rfl, ?_⟩
  intro representation computation
  apply OrderIso.ext
  funext event
  exact computation event

#print axioms observable_event_algebra_representation

end D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraRepresentation
