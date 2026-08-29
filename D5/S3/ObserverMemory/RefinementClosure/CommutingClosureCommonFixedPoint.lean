/- GID: D5/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/CommutingClosureCommonFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two commuting closure operators compose to a closure whose fixed points are exactly their common fixed points. -/

import Mathlib.Order.Closure

/- Library-search audit trail (2026-08-29):
   * Pinned Mathlib's `ClosureOperator` supplies monotonicity, extensivity,
     idempotence, and the `mk'` constructor.
   * Repository search found theory prose about commuting closures, but no
     machine-checked binary composition and fixed-point intersection theorem.
   * This module proves the finite two-operator case; transfinite iteration for
     arbitrary noncommuting families remains outside this owner.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.CommutingClosureCommonFixedPoint

universe u

/-- The one-pass composition of two commuting closure operators. -/
def commutingComposition
    {α : Type u} [PartialOrder α]
    (first second : ClosureOperator α)
    (commute : Function.Commute first second) : ClosureOperator α :=
  ClosureOperator.mk'
    (fun x => first (second x))
    (fun _ _ hxy => first.monotone (second.monotone hxy))
    (fun x => (second.le_closure x).trans (first.le_closure (second x)))
    (fun x => by
      apply le_of_eq
      calc
        first (second (first (second x))) =
            first (first (second (second x))) :=
          congrArg first (commute (second x)).symm
        _ = first (second (second x)) := first.idempotent _
        _ = first (second x) := congrArg first (second.idempotent x))

@[simp] theorem commutingComposition_apply
    {α : Type u} [PartialOrder α]
    (first second : ClosureOperator α)
    (commute : Function.Commute first second) (x : α) :
    commutingComposition first second commute x = first (second x) := by
  rfl

/-- A point is fixed by the commuting composition exactly when it is fixed by
both constituent closures. -/
theorem commuting_closure_composition_fixed_iff
    {α : Type u} [PartialOrder α]
    (first second : ClosureOperator α)
    (commute : Function.Commute first second) (x : α) :
    commutingComposition first second commute x = x <->
      first x = x ∧ second x = x := by
  constructor
  · intro compositionFixed
    have secondLe : second x <= x := by
      calc
        second x <= first (second x) := first.le_closure (second x)
        _ = x := compositionFixed
    have secondFixed : second x = x :=
      le_antisymm secondLe (second.le_closure x)
    have firstFixed : first x = x := by
      simpa [secondFixed] using compositionFixed
    exact ⟨firstFixed, secondFixed⟩
  · rintro ⟨firstFixed, secondFixed⟩
    simp [firstFixed, secondFixed]

/-- Commutativity makes the one-pass common closure independent of order. -/
theorem commuting_composition_order_independent
    {α : Type u} [PartialOrder α]
    (first second : ClosureOperator α)
    (commute : Function.Commute first second) (x : α) :
    commutingComposition first second commute x =
      commutingComposition second first commute.symm x := by
  exact commute x

/-- The identity closure commutes with and leaves every closure unchanged. -/
example {α : Type u} [PartialOrder α]
    (closure : ClosureOperator α) (x : α) :
    commutingComposition closure (ClosureOperator.id α)
        (by intro value; simp) x = closure x := by
  rfl

#print axioms commuting_closure_composition_fixed_iff
#print axioms commuting_composition_order_independent

end D5.S3.ObserverMemory.RefinementClosure.CommutingClosureCommonFixedPoint
