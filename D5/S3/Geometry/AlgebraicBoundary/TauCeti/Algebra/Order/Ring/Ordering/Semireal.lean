/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Ordering/Semireal
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Order/Ring/Ordering/Semireal
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Order/Ring/Ordering/Semireal.lean.
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

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Order.Ring.Ordering.Extension
public import Mathlib.Algebra.Ring.Semireal.Defs

/-! # Ordering formally real fields

The sums of squares in a formally real field form a preordering, which extends to an ordering.
This supplies an order when deriving polynomial intermediate value from `IsRealClosed`.

## References

Salma Kuhlmann,
[Real Algebraic Geometry, Lecture 3](https://www.math.uni-konstanz.de/algebra/WS0910/Notes03.pdf),
Corollary 3.4.
-/

public section

namespace RingPreordering

variable {K : Type*} [CommRing K]

/-- The sums of squares form a proper preordering in a formally real commutative ring. -/
def sumSq [IsSemireal K] : RingPreordering K where
  __ := Subsemiring.sumSq K
  mem_of_isSquare' hx := by simpa using hx.isSumSq
  neg_one_notMem' := by simpa using IsSemireal.not_isSumSq_neg_one K

end RingPreordering

/-- A formally real field admits a compatible linear order. -/
theorem IsSemireal.exists_linearOrder {K : Type*} [Field K] [IsSemireal K] :
    ∃ o : LinearOrder K, letI := o
      IsStrictOrderedRing K := by
  obtain ⟨o, ho, _⟩ := RingPreordering.exists_linearOrder (RingPreordering.sumSq (K := K))
  exact ⟨o, ho⟩
