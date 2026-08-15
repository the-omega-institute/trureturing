/- GID: D5/S0/Rewriting/QuotientFutureRelation
   generality: G
   mirror-B: D5/B/S0/Rewriting/QuotientFutureRelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A preserved equivalence is recovered from all future quotient observations. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hit: `Quotient.eq'` characterizes equality of
     quotient classes by the underlying setoid relation.
   * Searches for the full future-quotient characterization found no exact
     declaration. Searches for preservation of an arbitrary relation by all
     iterates found only nearby function-iteration results, so that step is
     proved below by induction.
-/

namespace QuotientFutureRelation

/-- If a setoid is preserved by a self-map, equality of all future quotient
observations recovers exactly the original relation. -/
theorem quotient_future_relation_iff {Y : Type*} (tau : Y -> Y)
    (R : Setoid Y)
    (preserves : forall {y y'}, R y y' -> R (tau y) (tau y'))
    (y y' : Y) :
    (forall k : Nat,
      (Quotient.mk' ((tau^[k]) y) : Quotient R) =
        Quotient.mk' ((tau^[k]) y')) <-> R y y' := by
  constructor
  · intro h
    exact Quotient.eq'.mp (by simpa using h 0)
  · intro h k
    apply Quotient.eq'.mpr
    induction k with
    | zero => simpa using h
    | succ k ih =>
        simpa only [Function.iterate_succ_apply'] using preserves ih

/-- Boolean negation with equality supplies a concrete instance. -/
example (y y' : Bool) :
    (forall k : Nat,
      @Quotient.mk' Bool (Setoid.ker id) ((Bool.not^[k]) y) =
        @Quotient.mk' Bool (Setoid.ker id) ((Bool.not^[k]) y')) <->
      (Setoid.ker id) y y' := by
  apply quotient_future_relation_iff Bool.not (Setoid.ker id)
  intro a b h
  exact congrArg Bool.not h

end QuotientFutureRelation
