/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/Signed
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/RingTheory/Polynomial/Subresultant/Signed
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/RingTheory/Polynomial/Subresultant/Signed.lean.
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

public import D5.S3.Geometry.AlgebraicBoundary.TauCeti.RingTheory.Polynomial.Subresultant.DegreeDrop.Basic
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Data.Nat.Choose.Basic

/-!
# Signed principal subresultant coefficients

The signed principal coefficients used in real-root counting differ from the
Sylvester principal minors by a degree-dependent sign. `Polynomial.signedPsc`
records this normalization, including the leading coefficients above the smaller
formal bound. The two binomial terms and the column-block sign in the
Sylvester–Habicht conversion simplify to
`(-1) ^ (m - j).choose 2`.

The degree-drop identities retain the formal bounds and include the smaller
terminal index. Mapping coefficients commutes with the signed coefficients
without a degree-preservation assumption. The specialization formulas use
reducta taken before mapping, so they can be used with nullified leading terms.
These are the scalar coefficients for permanences-minus-variations formulas.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
  second edition, Chapter 4 (Sylvester–Habicht normalization).
* Q. Vermande, *Cylindrical Algebraic Decomposition in Coq/Rocq*, §3
  (`subresultantE` uses the signed normalization).
-/

public section

namespace TauCeti

open Polynomial

variable {R S : Type*} [CommRing R]

/-- Signed principal subresultant coefficients at fixed bounds. Inside the
subresultant range they are signed Sylvester minors. Above that range the
coefficients at the two input bounds are retained, and all other entries vanish.
The equal-bound terminal entry is `1`, including for zero inputs. -/
noncomputable def _root_.Polynomial.signedPsc (p q : R[X]) (m n j : ℕ) : R :=
  if j ≤ min m n then (-1) ^ (m - j).choose 2 * psc p q m n j
  else if j = m then p.coeff m
  else if j = n then q.coeff n
  else 0

/-- Within the subresultant range only the left-bound gap determines the sign. -/
@[simp]
theorem _root_.Polynomial.signedPsc_of_le (p q : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p q m n j = (-1) ^ (m - j).choose 2 * psc p q m n j := by
  simp [signedPsc, hj]

/-- Above the smaller bound only the two input-bound coefficients are retained. -/
@[simp]
theorem _root_.Polynomial.signedPsc_of_lt (p q : R[X]) {m n j : ℕ}
    (hj : min m n < j) :
    signedPsc p q m n j =
      if j = m then p.coeff m else if j = n then q.coeff n else 0 := by
  simp [signedPsc, hj.not_ge]

/-- Signed coefficients specialize at fixed bounds, even when degrees drop. -/
@[simp]
theorem _root_.Polynomial.signedPsc_map_map [CommRing S] (f : R →+* S)
    (p q : R[X]) (m n j : ℕ) :
    signedPsc (p.map f) (q.map f) m n j = f (signedPsc p q m n j) := by
  simp [signedPsc, apply_ite f]

/-- The smaller left bound has no sign correction; a larger left bound retains
the left input coefficient itself. -/
@[simp]
theorem _root_.Polynomial.signedPsc_left_bound (p q : R[X]) (m n : ℕ) :
    signedPsc p q m n m =
      if m ≤ n then p.coeff m ^ (n - m) else p.coeff m := by
  by_cases hmn : m ≤ n <;> simp [signedPsc, hmn]

/-- Scaling the right input scales its signed minor by the number of its columns. -/
theorem _root_.Polynomial.signedPsc_C_mul_right (p q : R[X]) (r : R) {m n j : ℕ}
    (hj : j ≤ min m n) :
    signedPsc p (C r * q) m n j = r ^ (m - j) * signedPsc p q m n j := by
  simp only [signedPsc_of_le _ _ hj, psc_C_mul_right]
  ring

/-- A zero right input makes an in-range signed minor vanish when its column
block is nonempty. This excludes the empty-determinant terminal case.
Not a simp lemma: `signedPsc_of_le` already rewrites its left-hand side. -/
theorem _root_.Polynomial.signedPsc_zero_right (p : R[X]) {m n j : ℕ}
    (hj : j ≤ min m n) (hjm : j < m) : signedPsc p 0 m n j = 0 := by
  have h := signedPsc_C_mul_right p (0 : R[X]) 0 hj
  simpa [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hjm))] using h

end TauCeti
