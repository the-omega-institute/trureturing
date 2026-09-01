/- GID: D5/S3/Arith/Congruence/ObserverCollisionOrder
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ObserverCollisionOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observer collision order is the p-adic valuation and has a nontrivial witness. -/

import D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open with empty `coverage_gids` and no
     formalization receipt. Searches in D5, including the ZetaLinear, Pick,
     Observer, and ConceptDynamics families, found no collision-order declaration.
   * `PadicPrecisionBlindSpot.precision_reading_eq_iff_le_padicValInt` is a
     strict generalization: it characterizes agreement at every precision.
     This module imports that theorem and proves only the source-facing corollary.
   * Pinned Mathlib supplies `padicValInt`, `padicValInt_dvd_iff`, and the
     prime-power valuation API. It has no observer collision-order declaration.
   * Searches across all other pinned Lean packages found no reusable result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.ObserverCollisionOrder

open D5.S3.Arith.Congruence.PadicPrecisionBlindSpot

/-- If two integer readings agree modulo `p ^ r` but disagree modulo
`p ^ (r + 1)`, their collision order is exactly the `p`-adic valuation of
their difference. The second conjunct realizes the definition at order two,
so the defining conditions are nonempty at a positive, nontrivial order. -/
theorem observer_collision_order_eq_padic_valuation_and_exists :
    (∀ (p r : Nat) (a b : Int), p.Prime ->
      precisionReading p r a = precisionReading p r b ->
      precisionReading p (r + 1) a ≠ precisionReading p (r + 1) b ->
      padicValInt p (a - b) = r) ∧
    ∃ (p r : Nat) (a b : Int),
      p.Prime ∧ 1 ≤ r ∧
        precisionReading p r a = precisionReading p r b ∧
        precisionReading p (r + 1) a ≠ precisionReading p (r + 1) b ∧
        padicValInt p (a - b) = r := by
  have collisionOrder :
      ∀ (p r : Nat) (a b : Int), p.Prime ->
        precisionReading p r a = precisionReading p r b ->
        precisionReading p (r + 1) a ≠ precisionReading p (r + 1) b ->
        padicValInt p (a - b) = r := by
    intro p r a b hp sameAtOrder differentAtSuccessor
    have hab : a ≠ b := by
      intro hab
      subst b
      exact differentAtSuccessor rfl
    have orderLe : r ≤ padicValInt p (a - b) :=
      (precision_reading_eq_iff_le_padicValInt p r a b hp hab).mp sameAtOrder
    have successorNotLe : ¬(r + 1 ≤ padicValInt p (a - b)) := by
      intro successorLe
      exact differentAtSuccessor
        ((precision_reading_eq_iff_le_padicValInt p (r + 1) a b hp hab).mpr successorLe)
    omega
  refine ⟨collisionOrder, ?_⟩
  have sameAtTwo : precisionReading 2 2 0 = precisionReading 2 2 4 := by
    norm_num [precisionReading]
  have differentAtThree : precisionReading 2 3 0 ≠ precisionReading 2 3 4 := by
    norm_num [precisionReading]
  refine ⟨2, 2, 0, 4, by decide, by norm_num, sameAtTwo, differentAtThree, ?_⟩
  exact collisionOrder 2 2 0 4 (by decide) sameAtTwo differentAtThree

#print axioms observer_collision_order_eq_padic_valuation_and_exists

end D5.S3.Arith.Congruence.ObserverCollisionOrder
