/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Square
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Square
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Order/Ring/Square.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Ring.Abs

/-! # Nonnegative square roots of square elements

A square in a linearly ordered ring has a nonnegative square root, by taking the absolute
value of any square root. Only compatibility of the order with addition is needed.
-/

public section

/-- A square in a linearly ordered ring has a nonnegative square root. -/
theorem IsSquare.exists_nonneg_sq {R : Type*} [Ring R] [LinearOrder R]
    [IsOrderedAddMonoid R] {a : R} (ha : IsSquare a) : ∃ r : R, 0 ≤ r ∧ r ^ 2 = a := by
  obtain ⟨r, hr⟩ := ha.exists_sq
  exact ⟨|r|, abs_nonneg r, by simpa using hr.symm⟩
