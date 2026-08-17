/- GID: D5/S1/Eigenstructure/UnitJordanDrift
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/UnitJordanDrift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A unit Jordan block accumulates its fixed coordinate as linear drift. -/

import Mathlib.Algebra.Group.Basic

/- Library-search audit trail (2026-08-17):
   * Repository searches found no unit-Jordan iterate or linear-drift declaration.
   * Pinned-Mathlib searches found no packaged Jordan-block power formula.
   * `Function.iterate_succ_apply'` and `succ_nsmul` are reused for the induction step.
   * LeanSearch failed to return a response; Loogle reported the query identifier unknown. -/

namespace D5.S1.Eigenstructure.UnitJordanDrift

/-- The additive action of the two-dimensional unit Jordan block. -/
def unitJordanStep {A : Type*} [Add A] (v : A × A) : A × A :=
  (v.1 + v.2, v.2)

/-- Iterating a unit Jordan block produces exact linear drift in its first coordinate. -/
theorem unit_jordan_iterate_eq_linear_drift {A : Type*} [AddMonoid A]
    (x y : A) (n : ℕ) :
    (unitJordanStep^[n]) (x, y) = (x + n • y, y) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [unitJordanStep, succ_nsmul, add_assoc]

#print axioms unit_jordan_iterate_eq_linear_drift

end D5.S1.Eigenstructure.UnitJordanDrift
