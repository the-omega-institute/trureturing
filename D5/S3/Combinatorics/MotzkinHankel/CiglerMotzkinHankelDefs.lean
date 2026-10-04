/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs
   mirror-E: none(waiver:fixed-boundary-motzkin-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.RingTheory.PowerSeries.Basic, mathlib/module/Mathlib.Algebra.MvPolynomial.Basic, mathlib/module/Mathlib.Algebra.Polynomial.Degree.Defs]
   utility: none
   digest: Cigler's denominator and numerator degree for boundary-weighted Motzkin Hankel series. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

open Polynomial

/-! Fixed public statement: Cigler, *Some remarks and conjectures about Hankel determinants of
    polynomials which are related to Motzkin paths*, arXiv:2204.09910v4, §2, Conjecture 2.1,
    equation (2.3).  `M_{n,k}(t,s)` is the weighted number of Motzkin paths from `(0,0)` to `(n,k)`
    never below the axis, with up and down steps of weight `1`, horizontal steps of weight `s` at
    height `0` and `t` above.  `d_m(n,t,s) = det (M_{m+i+j,0}(t,s))_{0 ≤ i,j < n}`.  The conjecture:
    `∑ₙ d_m(n,t,s) xⁿ = R_m(x,t,s) / ∏_{j=0}^{⌊m/2⌋} A_{0,m-2j}(x,t)^{1+j(m-j)}` with `R_m` an
    integer polynomial in `x, s, t` of `x`-degree `binom(m+1,3) + 1`, where `A_{0,0} = 1 - x`,
    `A_{0,r} = 1 - L_r(t) x + x²` for `r > 0`, and `L_0 = 2`, `L_1 = t`,
    `L_r = t L_{r-1} - L_{r-2}`.  We work over `ℤ[t, s] = MvPolynomial (Fin 2) ℤ`. -/

/-- The coefficient ring `ℤ[t, s]`. -/
abbrev Base := MvPolynomial (Fin 2) ℤ

/-- The indeterminate `t`. -/
noncomputable def tVar : Base := MvPolynomial.X 0

/-- The indeterminate `s`. -/
noncomputable def sVar : Base := MvPolynomial.X 1

/-- `M_{n,k}(t,s)`, by the last step of the path. -/
noncomputable def motzkin : ℕ → ℕ → Base
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k =>
      (if k = 0 then 0 else motzkin n (k - 1)) + (if k = 0 then sVar else tVar) * motzkin n k +
        motzkin n (k + 1)

/-- The Hankel determinant `d_m(n,t,s)`. -/
noncomputable def hankelDet (m n : ℕ) : Base :=
  (Matrix.of fun i j : Fin n => motzkin (m + i + j) 0).det

/-- The Lucas-type polynomials `L_r(t)`. -/
noncomputable def lucas : ℕ → Base
  | 0 => 2
  | 1 => tVar
  | r + 2 => tVar * lucas (r + 1) - lucas r

/-- `A_{0,r}(x,t)` as a polynomial in `x` over `ℤ[t,s]`. -/
noncomputable def factorA (r : ℕ) : Base[X] :=
  if r = 0 then 1 - X else 1 - C (lucas r) * X + X ^ 2

/-- The denominator `∏_{j=0}^{⌊m/2⌋} A_{0,m-2j}(x,t)^{1+j(m-j)}`. -/
noncomputable def denominator (m : ℕ) : Base[X] :=
  ∏ j ∈ Finset.range (m / 2 + 1), factorA (m - 2 * j) ^ (1 + j * (m - j))

/-- Conjecture 2.1: for every `m ≥ 1` the denominator times the generating series is a polynomial
    `R_m` in `x` over `ℤ[t,s]` of degree `binom(m+1,3) + 1`. -/
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ R : Base[X],
    (R : PowerSeries Base) = (denominator m : PowerSeries Base) * PowerSeries.mk (hankelDet m) ∧
      R.natDegree = (m + 1).choose 3 + 1

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs
