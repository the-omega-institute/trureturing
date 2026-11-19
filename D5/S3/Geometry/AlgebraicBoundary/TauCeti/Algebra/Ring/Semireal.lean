/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Ring/Semireal
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Ring/Semireal
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Ring/Semireal.lean.
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

public import Mathlib.Algebra.Ring.Semireal.Defs

/-! # Square obstructions in semireal rings

Semireality excludes `-1` from the squares. The `Fact` instance supplies this obstruction
when constructing a field by adjoining a square root of `-1`.
-/

public section

namespace TauCeti

/-- In a semireal additive group with multiplication and a distinguished `1`, `-1` is not a square.
This supplies the square obstruction used by quadratic-algebra field instances. -/
instance {R : Type*} [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    Fact (¬ IsSquare (-1 : R)) :=
  ⟨fun h => IsSemireal.not_isSumSq_neg_one R h.isSumSq⟩

end TauCeti
