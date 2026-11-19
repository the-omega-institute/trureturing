/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Geometry/RealAlgebraic/SignDetermination/Defs.lean.
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

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Data.Fintype.Fiber
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Sign.Defs

/-! # Polynomial sign counts and Tarski queries

`Finset.signCount` counts the points of a finite set realizing a given polynomial
sign condition. `Finset.signSum` sums a polynomial's signs on that set.
`Polynomial.tarskiQuery p q` specializes the sum to the distinct roots of `p`.
For nonzero `p` its cardinality characterization counts the actual zeros of `p`;
for `p = 0` the value is zero and does not describe the infinite zero set.

The definitions and their basic API are independent of matrix inversion.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for sign conditions and Tarski queries.
-/

public section

open Polynomial SignType

namespace Finset

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, (sign (p.eval x.val) : ℤ)

/-- Sign sums expressed directly over the original finite set. -/
theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x ∈ Z, (sign (p.eval x) : ℤ) := by
  exact Finset.sum_coe_sort Z (fun x : R => (sign (p.eval x) : ℤ))

end Basic

end Finset

namespace Polynomial

open Finset

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

/-- The Tarski query expressed as a sum over distinct polynomial roots. -/
theorem tarskiQuery_eq_sum (p q : R[X]) :
    tarskiQuery p q = ∑ x ∈ p.roots.toFinset, (sign (q.eval x) : ℤ) := by
  exact signSum_eq_sum _ _

end Basic

end Polynomial
