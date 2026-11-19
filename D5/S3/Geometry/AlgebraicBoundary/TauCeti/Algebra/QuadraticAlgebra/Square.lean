/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/QuadraticAlgebra/Square
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/QuadraticAlgebra/Square
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/QuadraticAlgebra/Square.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
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

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Order.Ring.Square
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Square roots in quadratic complexifications

Every element of `QuadraticAlgebra R (-1) 0` is a square when `R` is an ordered field whose
nonnegative elements are squares. The algebraic formula uses two nonnegative square roots
in `R`, without completeness or an Archimedean assumption.
-/

public section

namespace QuadraticAlgebra

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

end QuadraticAlgebra
