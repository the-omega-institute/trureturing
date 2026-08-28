/- GID: D5/S3/ContinuousObservables/ObserverHorizonRefinement
   generality: G
   mirror-B: D5/B/S3/ContinuousObservables/ObserverHorizonRefinement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Refinement can only enlarge the infinite-distance observer horizon. -/

import D5.S3.Observer.Separation.RefinementDistanceMonotonicity

/- Library-search audit trail (2026-08-28):
   * The canonical `observerDistance` and exact refinement inequality are imported from
     `RefinementDistanceMonotonicity`; no second distance or horizon definition is introduced.
   * Repository searches found permutation-specific horizon sets, but no general theorem
     identifying refinement with inclusion of the top-distance fibers.
   * Pinned Mathlib supplies complete-lattice top uniqueness; no exact observer theorem exists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ContinuousObservables.ObserverHorizonRefinement

open D5.S3.Observer.Separation.RefinementDistanceMonotonicity

/-- Enlarging the observable family while preserving all old costs includes the old
infinite-distance horizon in the refined horizon. -/
theorem observer_horizon_mono_of_refinement
    {Observable State : Type*}
    (evaluate : State -> Observable -> Real) (origin : State)
    {oldObservables newObservables : Set Observable}
    {oldSeminorm newSeminorm : Observable -> ENNReal}
    (familyInclusion : oldObservables ⊆ newObservables)
    (costRestriction : forall (f : Observable), f ∈ oldObservables ->
      newSeminorm f = oldSeminorm f) :
    {x | observerDistance oldObservables oldSeminorm evaluate origin x = ⊤} ⊆
      {x | observerDistance newObservables newSeminorm evaluate origin x = ⊤} := by
  intro x oldHorizon
  have distanceMonotone :=
    observer_distance_mono_of_refinement evaluate origin x
      familyInclusion costRestriction
  rw [oldHorizon] at distanceMonotone
  exact top_unique distanceMonotone

example :
    (∅ : Set Unit) ⊆ Set.univ /\
      forall (f : Unit), f ∈ (∅ : Set Unit) -> (0 : ENNReal) = 0 := by
  simp

#print axioms observer_horizon_mono_of_refinement

end D5.S3.ContinuousObservables.ObserverHorizonRefinement
