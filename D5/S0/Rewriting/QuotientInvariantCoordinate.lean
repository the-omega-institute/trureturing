/- GID: D5/S0/Rewriting/QuotientInvariantCoordinate
   generality: G
   mirror-B: D5/B/S0/Rewriting/QuotientInvariantCoordinate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A complete invariant gives an injective coordinate on equivalence classes. -/

/- Library-search audit trail (2026-08-13):
   * Exact pinned-Mathlib hit: `Setoid.lift_injective_iff_ker_eq_of_le`
     characterizes injectivity of a relation-respecting map on a quotient.
   * Supporting hits: `Setoid.kerLift_injective`,
     `Setoid.ker_eq_lift_of_injective`, `Quotient.exact`, and
     `Quotient.sound`.
   * Searches for a complete-invariant quotient coordinate theorem found no
     exact local declaration. The proof below is a thin wrapper around the
     exact pinned-Mathlib characterization.
-/

import Mathlib.Data.Setoid.Basic

namespace QuotientInvariantCoordinate

/-- A complete invariant descends to an injective coordinate on equivalence
classes. This closes only the quotient-coordinate clause; existence of
canonical representatives and metatheoretic classification claims are not
asserted. -/
theorem quotient_invariant_coordinate_injective {α β : Type*} (r : Setoid α)
    (f : α → β) (complete : ∀ x y, f x = f y ↔ r x y) :
    Function.Injective
      (Quotient.lift f (fun x y hxy => (complete x y).2 hxy)) := by
  apply (Setoid.lift_injective_iff_ker_eq_of_le _).2
  ext x y
  exact complete x y

/-- Distinct parity classes receive distinct coordinates. -/
example :
    let r : Setoid Nat := Setoid.ker (fun n => n % 2)
    let coordinate : Quotient r → Nat := Setoid.kerLift (fun n => n % 2)
    coordinate ⟦0⟧ ≠ coordinate ⟦1⟧ := by
  simp [Setoid.kerLift]

end QuotientInvariantCoordinate
