/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Data/SignType/Parity
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Data/SignType/Parity
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Data/SignType/Parity.lean.
Adaptation: ordinary D5 import routes; the original declarations and proofs are retained.
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

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Basic.Sign.Basic

/-!
# Sign changes twisted by powers of `-1`

Sturm-type counts compare the signs of consecutive entries at `+∞` and at `-∞`. At `-∞` a
leading sign `s` of a degree-`m` polynomial becomes `s * (-1) ^ m`. For nonzero signs `s` and
`t`, the sign-change indicator of the twisted pair minus that of the original pair is `s * t`
when `m + n` is odd and `0` otherwise.

## Main results

* `SignType.ite_mul_neg_one_pow_sub_ite`: the difference of the two sign-change indicators.
-/

public section

namespace TauCeti

/-- Comparing the nonzero signs `s * (-1) ^ m` and `t * (-1) ^ n` instead of `s` and `t`
changes the sign-change indicator by `s * t` exactly when `m + n` is odd. -/
theorem _root_.SignType.ite_mul_neg_one_pow_sub_ite (m n : ℕ) {s t : SignType} (hs : s ≠ 0)
    (ht : t ≠ 0) :
    ((if s * (-1) ^ m = t * (-1) ^ n then 0 else 1 : ℕ) : ℤ) -
        ((if s = t then 0 else 1 : ℕ) : ℤ) =
      if Odd (m + n) then (s : ℤ) * t else 0 := by
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn <;>
    simp only [hm.neg_one_pow, hn.neg_one_pow, Nat.odd_add, hm, hn, mul_one, mul_neg] <;>
    cases s <;> cases t <;> simp_all [Nat.not_odd_iff_even.mpr, Nat.not_even_iff_odd.mpr]

end TauCeti
