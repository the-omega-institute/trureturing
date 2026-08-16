/- GID: D5/S3/Zeros/Symmetry/OrbitStabilizerMultiplicity
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/OrbitStabilizerMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Orbit size in a four-element group action is four divided by stabilizer size. -/

/- Library-search audit trail (2026-08-16):
   * D5 searches for orbit-stabilizer cardinality formulas found no equivalent declaration.
   * A natural-language smart search returned no declaration-name hit.
   * An identifier search found the exact pinned-Mathlib theorem
     `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, imported and specialized below.
-/

import Mathlib.GroupTheory.GroupAction.Quotient

namespace D5.S3.Zeros.Symmetry.OrbitStabilizerMultiplicity

/-- In an action by a four-element group, an orbit has size four divided by the size of the
stabilizer. This closes only the orbit-stabilizer multiplicity clause of the source atom. -/
theorem orbit_card_eq_four_div_stabilizer_card {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] (x : X) [Fintype (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)] (hG : Fintype.card G = 4) :
    Fintype.card (MulAction.orbit G x) =
      4 / Fintype.card (MulAction.stabilizer G x) := by
  apply Nat.eq_div_of_mul_eq_right Fintype.card_ne_zero
  simpa only [hG, Nat.mul_comm] using
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x

/-- A point with trivial stabilizer has a four-element orbit. -/
example {G X : Type*} [Group G] [MulAction G X] [Fintype G]
    (x : X) [Fintype (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)] (hG : Fintype.card G = 4)
    (hStabilizer : Fintype.card (MulAction.stabilizer G x) = 1) :
    Fintype.card (MulAction.orbit G x) = 4 := by
  simpa [hStabilizer] using orbit_card_eq_four_div_stabilizer_card x hG

#print axioms orbit_card_eq_four_div_stabilizer_card

end D5.S3.Zeros.Symmetry.OrbitStabilizerMultiplicity
