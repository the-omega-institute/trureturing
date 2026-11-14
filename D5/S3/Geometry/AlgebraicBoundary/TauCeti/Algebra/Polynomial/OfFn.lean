/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/OfFn
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/OfFn
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Polynomial/OfFn.lean.
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

public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Recovering a polynomial of bounded degree from its coefficient vector

`Polynomial.ofFn n` and `Polynomial.toFn n` pass between vectors of length `n` and polynomials.
Mathlib records that a polynomial of `natDegree` below `n` is recovered from its first `n`
coefficients; this file states the same recovery in terms of `degree`, so that it also applies
to the zero polynomial. This file also records evaluation of the coefficient vector and
reconstruction of a coordinate vector as a power of `X`.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

omit [DecidableEq R] in
/-- Evaluating the coefficient vector reads the corresponding polynomial coefficient. -/
@[simp]
theorem _root_.Polynomial.toFn_apply (n : ℕ) (p : R[X]) (i : Fin n) :
    toFn n p i = p.coeff i := (rfl)

-- Mathlib's `ofFn` takes `[DecidableEq R]`, so this instance occurs in the statement.
/-- The coordinate vector with value one at `l` reconstructs the monomial `X ^ l.val`. -/
@[simp]
theorem _root_.Polynomial.ofFn_single {n : ℕ} (l : Fin n) :
    ofFn n (fun i => if i = l then (1 : R) else 0) = X ^ l.val := by
  simp [ofFn_eq_sum_monomial, apply_ite (monomial _), monomial_one_right_eq_X_pow]

/-- A polynomial of degree below `n` is recovered from its vector of first `n` coefficients.
This is the `degree` form of `Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt`, which also covers
the zero polynomial. -/
theorem _root_.Polynomial.ofFn_comp_toFn_eq_id_of_degree_lt {n : ℕ} {p : R[X]} (h : p.degree < n) :
    ofFn n (toFn n p) = p := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · exact ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt hp).mpr h)

end TauCeti
