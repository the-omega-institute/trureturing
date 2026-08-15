/- GID: D5/S3/Observer/Separation/FiniteDistanceInvariantSector
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/FiniteDistanceInvariantSector
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite distance forces equal evaluation on bounded invariant observables. -/

import D5.S3.Observer.Separation.InvariantObservableInfinity

/- Library-search audit trail (2026-08-16):
   * Repository searches for finite observer distance, invariant sectors, and equality on
     update-invariant observables found no matching D5 declaration.
   * The repository theorem `invariant_separation_distance_eq_top` is the exact
     contrapositive dependency and is imported and applied below.
   * Pinned-Mathlib searches for finite extended-distance components and separation by
     invariant observables found no matching theorem.
   * Loogle searches for the observer-distance statement found no exact match. -/

namespace D5.S3.Observer.Separation.FiniteDistanceInvariantSector

open D5.S3.Observer.ObserverMetric
open D5.S3.Observer.Separation.InvariantObservableInfinity

/-- Points at finite observer distance have the same evaluation on every bounded
update-invariant observable, so each finite-distance component lies in one invariant sector. -/
theorem finite_distance_same_invariant_sector {index : Type*}
    (tau : Equiv.Perm index) (x y : index)
    (hfinite : invariantObserverDistance tau x y ≠ ⊤) :
    forall f : index -> Complex,
      Bornology.IsBounded (Set.range f) ->
      updateDefect tau f = 0 ->
      f x = f y := by
  intro f hbounded hinvariant
  by_contra hseparates
  exact hfinite
    (invariant_separation_distance_eq_top tau f x y hbounded hinvariant hseparates)

/-- The finite-distance hypothesis is inhabited on a concrete finite domain. -/
example :
    invariantObserverDistance (Equiv.refl Bool) false false ≠ ⊤ := by
  simp [invariantObserverDistance]

#print axioms finite_distance_same_invariant_sector

end D5.S3.Observer.Separation.FiniteDistanceInvariantSector
