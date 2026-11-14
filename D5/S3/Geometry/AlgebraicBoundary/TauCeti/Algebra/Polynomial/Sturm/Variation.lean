/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Sturm/Variation
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/Sturm/Variation
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Polynomial/Sturm/Variation.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.Polynomial.Sturm.Signs

/-!
# Variations of a Sturm sequence at a point

The variation of a signed Euclidean remainder sequence is the number used in
Sturm's root-counting formula. Mathlib's `Polynomial.sturmSeq` supplies the
sequence and `TauCeti.Sturm.signVariationsAt` counts its evaluated sign changes.
At a zero of the nonzero second polynomial where the first is nonzero, the first and third
values are opposite, so deleting the zero reveals exactly one sign change. This file
records that local calculation alongside the sequence recurrence. The existing
empty-list and singleton variation lemmas supply the zero cases. The calculation works over
any ordered field; it does not require real closedness.
Negating both inputs or multiplying them by a polynomial nonzero at the
evaluation point leaves the variation unchanged, while a common root makes it zero.
The evaluated variation uses the existing `TauCeti.Sturm.signVariationsAt` API
on `Polynomial.sturmSeq p q`.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K]

/-- Evaluation of the first entry gives the recursion for Sturm variations. -/
private theorem signVariationsAt_sturmSeq_cons {p : K[X]} (hp : p ≠ 0) (q : K[X]) (x : K) :
    signVariationsAt (sturmSeq p q) x =
      (p.eval x :: (sturmSeq q (-p % q)).map (fun r => r.eval x)).signVariations := by
  simp only [signVariationsAt_def, sturmSeq_cons hp, List.map_cons]

/-- When the first two evaluations are nonzero, a Sturm variation step adds
one exactly when their signs differ. -/
theorem signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq : q.eval x ≠ 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x +
      (if SignType.sign (p.eval x) = SignType.sign (q.eval x) then 0 else 1) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  rw [signVariationsAt_sturmSeq_cons hp0, signVariationsAt_sturmSeq_cons hq0, sturmSeq_cons hq0,
    List.map_cons, List.signVariations_cons_cons_of_ne_zero _ hp hq]

end TauCeti.Sturm
