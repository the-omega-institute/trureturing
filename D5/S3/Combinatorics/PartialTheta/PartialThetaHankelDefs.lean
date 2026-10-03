/- GID: D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs
   mirror-E: none(waiver:fixed-partial-theta-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Degree.Defs, mathlib/module/Mathlib.Algebra.Polynomial.Eval.Defs]
   utility: none
   digest: Cigler's conjecture on Hankel determinants of shifted partial theta coefficients. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PartialTheta.PartialThetaHankelDefs

open Polynomial

/-! Fixed public statement: Cigler, *Hankel determinants of backward shifts of the coefficients
    of a partial theta function*, arXiv:2407.05768v2, §1, the Conjecture after equation (2).
    With `a(s, q) = q^{binom(s,2)}` for `s ≥ 0` and `a(s, q) = 0` for `s < 0`, and
    `D_{-m,N}(q) = det (a(-m+i+j, q))_{0 ≤ i, j < N}`, equation (2) defines `r_{m,n}(q)` by
    `D_{-m,n+m+1}(q) = (-1)^{binom(m+1,2)} r_{m,n}(q) q^{m binom(n,2)} D_{0,n+1}(q)`.  The
    conjecture: `r_{m,n}` is a monic polynomial with integer coefficients of degree
    `mn(n+m+2)/2`, with `r_{m,n}(1) = 1` and `r_{m,n}(0) = (-1)^{mn}`. -/

/-- The coefficient `a(s, q)`. -/
noncomputable def coeffA (s : ℤ) : ℤ[X] := if 0 ≤ s then X ^ s.toNat.choose 2 else 0

/-- The Hankel determinant `D_{-m,N}(q)`. -/
noncomputable def hankel (m N : ℕ) : ℤ[X] :=
  (Matrix.of fun i j : Fin N => coeffA (-(m : ℤ) + (i : ℕ) + (j : ℕ))).det

/-- The Conjecture: for all `m, n`, `D_{0,n+1} ≠ 0` (so that (2) determines `r_{m,n}`), and the
    `r_{m,n}` of (2) is a monic integer polynomial with the stated degree and values. -/
def claim : Prop :=
  ∀ m n : ℕ, hankel 0 (n + 1) ≠ 0 ∧
    ∃ r : ℤ[X],
      hankel m (n + m + 1) =
          (-1) ^ (m + 1).choose 2 * r * X ^ (m * n.choose 2) * hankel 0 (n + 1) ∧
        r.Monic ∧ r.natDegree = m * n * (n + m + 2) / 2 ∧ r.eval 1 = 1 ∧
        r.eval 0 = (-1) ^ (m * n)

end D5.S3.Combinatorics.PartialTheta.PartialThetaHankelDefs
