/- GID: D5/S3/ContinuousObservables/AsymmetricPermutationDistances
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/AsymmetricPermutationDistances
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two permutations yield infinite and finite observer distances. -/

import D5.S3.ContinuousObservables.PermutationOrbitHorizon

/- Library-search audit trail (2026-08-28):
   * The local Mathlib tree has no declarations named for observer distance, edge
     admissibility, or signed permutation-orbit observer bounds.
   * Repository searches found the exact two source dependencies:
     `permutation_observer_distance_classification` gives the invariant-label
     infinite-distance clause, and `permutation_observer_horizon_eq_orbit_complement`
     gives the signed-orbit telescope bound.
   * No frozen declaration states both clauses for the same endpoints under two
     independently supplied permutations, so this module assembles those owners.
-/

open scoped ENNReal

namespace D5.S3.ContinuousObservables.AsymmetricPermutationDistances

open D5.S3.ContinuousObservables.ObserverDistanceClassification
open D5.S3.ContinuousObservables.PermutationOrbitHorizon

/-- An invariant label separates two points infinitely for one permutation, while a
signed orbit witness makes the same pair finitely reachable for another permutation. -/
theorem asymmetric_permutation_observer_distances
    {I Leaf : Type*} (tau tau' : Equiv.Perm I) (leaf : I -> Leaf)
    {x y : I} (hLeafInvariant : forall i, leaf (tau i) = leaf i)
    (hDifferent : leaf x ≠ leaf y) (n : Int)
    (hOrbit : x = (tau' ^ n) y) :
    observerDistance tau x y = ⊤ ∧
      observerDistance tau' x y <= (n.natAbs : ENNReal) ∧
      observerDistance tau' x y < ⊤ := by
  have hInfinite : observerDistance tau x y = ⊤ :=
    (permutation_observer_distance_classification
      tau leaf hLeafInvariant hDifferent (M := 1) 0 0 0 0).1
  have hFiniteBound :
      observerDistance tau' y x <= (n.natAbs : ENNReal) :=
    (permutation_observer_horizon_eq_orbit_complement tau' y x y).2.1 n hOrbit
  have hFiniteBound' :
      observerDistance tau' x y <= (n.natAbs : ENNReal) := by
    simpa [observerDistance, dist_comm] using hFiniteBound
  exact ⟨hInfinite, hFiniteBound', lt_of_le_of_lt hFiniteBound' (by simp)⟩

#print axioms asymmetric_permutation_observer_distances

end D5.S3.ContinuousObservables.AsymmetricPermutationDistances
