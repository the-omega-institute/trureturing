/- GID: D5/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/MatrixAnalysis/InverseOperatorConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-definite finite matrices satisfy weighted inverse operator convexity. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.MatrixAnalysis.InverseOperatorConvexity

open scoped MatrixOrder
open scoped ComplexOrder
open scoped Matrix.Norms.L2Operator

/-!
The repository-facing matrix form of operator convexity for inversion.  The
noncommutative content is supplied by Mathlib's C⋆-algebra theorem; the bridge
here identifies its strictly-positive domain with `Matrix.PosDef` and its
`Ring.inverse` with the nonsingular matrix inverse.
-/

theorem posDef_weighted_inverse_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • A + b • B)⁻¹ ≤ a • A⁻¹ + b • B⁻¹ := by
  have h := (CStarAlgebra.convexOn_ringInverse (A := Matrix n n ℂ)).2
    hA.isStrictlyPositive hB.isStrictlyPositive ha hb hab
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using h

end D5.S3.Quantum.MatrixAnalysis.InverseOperatorConvexity
