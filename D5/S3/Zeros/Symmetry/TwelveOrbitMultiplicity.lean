/- GID: D5/S3/Zeros/Symmetry/TwelveOrbitMultiplicity
   generality: G
   mirror-B: D5/B/S3/Zeros/Symmetry/TwelveOrbitMultiplicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Twelvefold symmetry counts equal orbits by their stabilizer. -/

/- Library-search audit trail (2026-08-17):
   * D5 searches found no equivalent twelvefold multi-orbit formula.
   * A natural-language smart search returned no declaration-name hit.
   * Pinned Mathlib provides the exact orbit-stabilizer identity
     `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, reused below.
-/

import Mathlib.GroupTheory.GroupAction.Quotient

namespace D5.S3.Zeros.Symmetry.TwelveOrbitMultiplicity

/-- If a finite set consists of `orbitCount` copies of one orbit under a twelve-element group,
then its multiplicity times the stabilizer size is `12 * orbitCount`; equivalently, its
multiplicity is `12 * orbitCount / |stabilizer|`. This closes only the multiplicity formula in
appendix E.78; the four numerical examples and oriented-class interpretation are not asserted. -/
theorem twelve_orbit_multiplicity {G X Y : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype Y] (x : X) [Finite (MulAction.orbit G x)]
    [Fintype (MulAction.stabilizer G x)] (orbitCount : ℕ)
    (decomposition : Y ≃ Fin orbitCount × MulAction.orbit G x)
    (hG : Fintype.card G = 12) :
    Fintype.card Y * Fintype.card (MulAction.stabilizer G x) = 12 * orbitCount ∧
      Fintype.card Y =
        12 * orbitCount / Fintype.card (MulAction.stabilizer G x) := by
  letI := Fintype.ofFinite (MulAction.orbit G x)
  have hY :
      Fintype.card Y = orbitCount * Fintype.card (MulAction.orbit G x) := by
    rw [Fintype.card_congr decomposition]
    simp
  have hmul :
      Fintype.card Y * Fintype.card (MulAction.stabilizer G x) = 12 * orbitCount := by
    rw [hY, mul_assoc,
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x, hG, Nat.mul_comm]
  refine ⟨hmul, ?_⟩
  apply Nat.eq_div_of_mul_eq_right Fintype.card_ne_zero
  simpa only [Nat.mul_comm] using hmul

#print axioms twelve_orbit_multiplicity

end D5.S3.Zeros.Symmetry.TwelveOrbitMultiplicity
