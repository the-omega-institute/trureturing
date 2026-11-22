/- GID: D5/S3/Arith/Additive/Waring/WaringFiniteDifference
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Third-party formalization of the qualitative Hilbert–Waring theorem. -/

/- Source: https://github.com/yunyougu50-create/waring-lean4/blob/cd0735c253f3b640262fcc74a61306cb41e23765/WaringFiniteDifference.lean#L1-L70
   Modified for this repository. Local imports use their D5 module paths.
   Full Apache-2.0 license: D5/S3/Arith/Additive/Waring/WaringStatement.lean. -/

/-
Copyright (c) 2026 The Waring formalization authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Waring formalization authors
-/
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Basic

/-!
# Finite differences for the Hilbert–Waring route

Mathlib already provides the forward difference operator and the Newton
binomial formula in `Mathlib/Algebra/Group/ForwardDiff.lean`.  This file
packages the special case `ℤ → ℤ` and the polynomial corollaries that the
Hilbert–Waring proof uses.

Main results:

* `Waring.diffN_apply`: the `k`-th forward difference is the alternating
  binomial sum of the values `f (x + i)`;
* `Waring.diffN_polynomial_eq_zero`: the `k`-th difference of a polynomial of
  degree `< k` is zero;
* `Waring.diffN_pow_eq_zero_of_lt`: the `k`-th difference of `x ↦ x^j` is zero
  for `j < k`;
* `Waring.diffN_pow_self`: the `k`-th difference of `x ↦ x^k` is `k!`.
-/

open Finset Polynomial

open scoped fwdDiff

namespace Waring

/-- The forward difference operator on `ℤ → ℤ`. -/
abbrev diff (f : ℤ → ℤ) : ℤ → ℤ := Δ_[1] f

/-- The `k`-th forward difference on `ℤ → ℤ`. -/
abbrev diffN (k : ℕ) (f : ℤ → ℤ) : ℤ → ℤ := Δ_[1]^[k] f

/-- The alternating binomial formula for the `k`-th forward difference. -/
theorem diffN_apply (k : ℕ) (f : ℤ → ℤ) (x : ℤ) :
    diffN k f x =
      ∑ i ∈ range (k + 1),
        (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * f (x + i) := by
  rw [show diffN k f x = Δ_[1]^[k] f x from rfl]
  rw [fwdDiff_iter_eq_sum_shift (h := (1 : ℤ)) f k x]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [mul_assoc]

/-- The `k`-th forward difference kills polynomials of degree `< k`. -/
theorem diffN_polynomial_eq_zero {P : ℤ[X]} {k : ℕ} (hP : P.natDegree < k) :
    diffN k (fun z => P.eval z) = 0 := by
  simpa [diffN, diff] using
    (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (R := ℤ) (P := P) (n := k) hP)

/-- The `k`-th forward difference of `x ↦ x^j` vanishes for `j < k`. -/
theorem diffN_pow_eq_zero_of_lt {j k : ℕ} (h : j < k) :
    diffN k (fun z : ℤ => z ^ j) = 0 := by
  simpa [diffN, diff] using
    (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) h)

/-- The `k`-th forward difference of `x ↦ x^k` is the constant `k!`. -/
theorem diffN_pow_self (k : ℕ) :
    diffN k (fun z : ℤ => z ^ k) = fun _ => (k.factorial : ℤ) := by
  ext x
  simpa [diffN, diff] using
    congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := k)) x

end Waring
