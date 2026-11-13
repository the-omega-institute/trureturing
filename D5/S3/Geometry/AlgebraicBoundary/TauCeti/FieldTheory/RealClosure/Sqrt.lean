/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/Sqrt
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/FieldTheory/RealClosure/Sqrt
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/FieldTheory/RealClosure/Sqrt.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Basic
public import Mathlib.Analysis.Real.Sqrt
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.FieldTheory.IsRealClosed.Real
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Order.Ring.Square

/-! # Nonnegative square roots in real closed fields

Every nonnegative element of an ordered real closed field has a unique nonnegative square root.
`nonnegSqrt` chooses this root, and on `ℝ` it agrees with `Real.sqrt`.

## Main results

* `nonnegSqrt` chooses the root using real closedness; `nonnegSqrt_nonneg`
  and `sq_nonnegSqrt` characterize it.
* `nonnegSqrt_real_eq_sqrt` identifies the chosen root on `ℝ` with `Real.sqrt`.
-/

public section

namespace TauCeti.RealClosure

section

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The nonnegative square root of a nonnegative element in a real closed field. -/
noncomputable def nonnegSqrt [IsRealClosed R] {a : R} (ha : 0 ≤ a) : R :=
  Classical.choose ((IsSquare.of_nonneg ha).exists_nonneg_sq)

/-- The selected square root is nonnegative. -/
@[simp]
theorem nonnegSqrt_nonneg
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    0 ≤ nonnegSqrt ha :=
  (Classical.choose_spec ((IsSquare.of_nonneg ha).exists_nonneg_sq)).1

/-- The selected square root squares to its input. -/
@[simp]
theorem sq_nonnegSqrt
    [IsRealClosed R] {a : R} (ha : 0 ≤ a) :
    (nonnegSqrt ha) ^ 2 = a :=
  (Classical.choose_spec ((IsSquare.of_nonneg ha).exists_nonneg_sq)).2

/-- The chosen nonnegative square root on `ℝ` agrees with `Real.sqrt`. -/
theorem nonnegSqrt_real_eq_sqrt
    {a : ℝ} (ha : 0 ≤ a) : nonnegSqrt ha = Real.sqrt a := by
  apply (sq_eq_sq₀ (nonnegSqrt_nonneg ha) (Real.sqrt_nonneg a)).mp
  rw [sq_nonnegSqrt, Real.sq_sqrt ha]

end

end TauCeti.RealClosure
