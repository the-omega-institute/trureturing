/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Nat/Choose/Basic
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Data/Nat/Choose/Basic
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Data/Nat/Choose/Basic.lean.
Adaptation: ordinary D5 import routes; retained declarations keep their original proofs.
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

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary identities for binomial coefficients

This file records arithmetic identities involving natural-number binomial coefficients.

Besides the second binomial coefficient of a sum, it develops Vandermonde's convolution
`∑ i, C(A, i) * C(B, r - i) = C(A + B, r)` in the shape taken by factorial moments of a law
supported on such a convolution: each summand is weighted by the falling factorial `(i)ₘ` of the
summation index. The weighted sum is again a single binomial coefficient,
`(A)ₘ * C(A + B - m, r - m)`, because `(i)ₘ` lowers both indices of `C(A, i)` at once.

The retained source supplies the useful proof dependencies. Further exact applications,
including their assumptions and boundary cases, are developed in the owning Blueprint.

## References

* R. L. Graham, D. E. Knuth, O. Patashnik, *Concrete Mathematics*, 2nd ed., Addison-Wesley, 1994,
  Section 5.1 (the absorption identity and Vandermonde's convolution, equation (5.27)).
-/

public section

open Finset

namespace Nat

/-- The second binomial coefficient of a sum: `C(m + n, 2) = C(m, 2) + C(n, 2) + mn`. -/
theorem add_choose_two (m n : ℕ) : (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : (m + (n + 1)).choose 2 = (m + n).choose 1 + (m + n).choose 2 := by
        rw [← Nat.add_assoc]
        exact Nat.choose_succ_succ (m + n) 1
      have h2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
      rw [h1, h2, ih, Nat.choose_one_right, Nat.choose_one_right]
      ring

end Nat
