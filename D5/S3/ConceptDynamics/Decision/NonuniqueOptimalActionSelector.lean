/- GID: D5/S3/ConceptDynamics/Decision/NonuniqueOptimalActionSelector
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/NonuniqueOptimalActionSelector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A determined two-action optimum needs an ordered tie-breaker to become single-valued. -/

import D5.S3.ConceptDynamics.Decision.PredictionDecisionSufficiency

/- Library-search audit trail (2026-08-27):
   * The imported decision-family owner supplies the canonical PMF, expected-loss integral, and
     full argmin-set semantics; this module uses those shapes rather than introducing a sibling
     runtime or optimizer definition.
   * Repository and Blueprint searches found no exact equal-risk countermodel carrying both
     nonuniqueness and the ordered-selector contrast.
   * Pinned Mathlib simplifies the integral of the zero loss and the cardinality of `Set.univ`
     on Bool, but has no theorem packaging the source's combined decision claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.NonuniqueOptimalActionSelector

open MeasureTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- A constant prediction with equal losses determines the complete optimizer set, but that set
contains both Boolean actions. Its least element is a unique deterministic selection only relative
to the added Boolean order, while the original optimizer set remains non-singleton. -/
theorem determined_optimal_set_can_be_nonunique :
    exists (prediction : Bool -> PMF Unit) (loss : Bool -> Unit -> Real),
      let expectedLoss : Bool -> Bool -> Real :=
        fun state action => integral (prediction state).toMeasure (loss action)
      let optimalActions : Bool -> Set Bool :=
        fun state => {action | forall alternative,
          expectedLoss state action <= expectedLoss state alternative}
      let concept : Concept Bool Unit := fun _ => ()
      let tieBrokenSelector : Bool -> Bool := fun _ => false
      Refines optimalActions concept /\
        (forall x, Set.ncard (optimalActions x) = 2) /\
        (forall x, tieBrokenSelector x ∈ optimalActions x) /\
        (forall x action, action ∈ optimalActions x ->
          tieBrokenSelector x <= action) /\
        (forall x selected, selected ∈ optimalActions x ->
          (forall action, action ∈ optimalActions x -> selected <= action) ->
          selected = tieBrokenSelector x) /\
        (forall x, exists action,
          action ∈ optimalActions x /\ action ≠ tieBrokenSelector x) := by
  refine ⟨fun _ => PMF.pure (), fun _ _ => 0, ?_⟩
  dsimp only
  constructor
  · refine ⟨fun _ => Set.univ, ?_⟩
    funext x
    ext action
    simp
  constructor
  · intro x
    have allActions :
        {action : Bool | forall alternative : Bool,
          integral (PMF.pure ()).toMeasure (fun _ => (0 : Real)) <=
            integral (PMF.pure ()).toMeasure (fun _ => (0 : Real))} = Set.univ := by
      ext action
      simp
    rw [allActions, Set.ncard_univ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  constructor
  · intro x
    simp
  constructor
  · intro x action actionOptimal
    cases action <;> decide
  constructor
  · intro x selected selectedOptimal selectedLeast
    have belowFalse := selectedLeast false (by simp)
    exact Bool.eq_false_of_le_false belowFalse
  · intro x
    exact ⟨true, by simp, by decide⟩

#print axioms determined_optimal_set_can_be_nonunique

end D5.S3.ConceptDynamics.Decision.NonuniqueOptimalActionSelector
