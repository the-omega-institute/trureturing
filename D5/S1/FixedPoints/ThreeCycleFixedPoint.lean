/- GID: D5/S1/FixedPoints/ThreeCycleFixedPoint
   generality: G
   mirror-B: D5/B/S1/FixedPoints/ThreeCycleFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An order-three permutation on a finite set of size one mod three has a fixed point. -/

/- Library-search audit trail (2026-08-16):
   * D5 searches for order-three permutation fixed-point results found no equivalent declaration.
   * The natural-language smart search returned no declaration-name hit (exit 1).
   * Loogle was reachable (HTTP 200); LeanSearch's `/api/search` endpoint returned HTTP 404.
   * Local pinned-Mathlib grep found `Equiv.Perm.exists_fixed_point_of_prime`, used below. -/

import Mathlib.GroupTheory.Perm.Cycle.Type

namespace D5.S1.FixedPoints.ThreeCycleFixedPoint

/-- An order-three permutation of a finite set whose cardinality is one modulo three fixes a
point. This closes only the fixed-point consequence in the P3 clause of the source atom. -/
theorem three_cycle_action_has_fixed_point
    {X : Type*} [Fintype X] (sigma : Equiv.Perm X)
    (horder : sigma ^ 3 = 1) (hcard : Fintype.card X % 3 = 1) :
    ∃ x : X, sigma x = x := by
  apply Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1)
  · intro hdiv
    have hz : Fintype.card X % 3 = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [hcard] at hz
    exact Nat.one_ne_zero hz
  · simpa using horder

#print axioms three_cycle_action_has_fixed_point

end D5.S1.FixedPoints.ThreeCycleFixedPoint
