/- GID: D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs
   mirror-E: none(waiver:fixed-motzkin-column-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Eval]
   utility: none
   digest: Cigler's reduced denominators and numerator degrees for Motzkin-column Hankel series. -/

import D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDefs

open Polynomial D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

/-! Fixed public statement: Cigler, *Some remarks and conjectures about Hankel determinants of
    polynomials which are related to Motzkin paths*, arXiv:2204.09910v4, §1, Conjecture 1.3,
    equation (1.30).  `M_{n,k}(t)` counts Motzkin paths from `(0,0)` to `(n,k)` with all horizontal
    steps of weight `t`, that is `motzkin n k` with `s = t`; `d_m^{(k)}(n,t)` is
    `det (M_{m+i+j,k}(t))_{0 ≤ i,j < n}` and `D_m^{(k)}(x,t) = ∑ₙ d_m^{(k)}(n,t) xⁿ`.  With
    `e = (-1)^{binom(k+1,2)}`, `A_{k,0} = 1 - e x^{k+1}` and
    `A_{k,r} = 1 - e L_r(t) x^{k+1} + x^{2(k+1)}` for `r > 0` (equation (1.28)).  The conjecture:
    `D_m^{(k)} = r_m^{(k)} / ∏_{j=0}^{⌊m/2⌋} A_{k,(k+1)(m-2j)}^{1+j(m-j)}` with `r_m^{(k)}` a
    polynomial of `x`-degree `binom(m+1,3) + k (binom(m,1) + binom(m,2) + binom(m,3))`. -/

/-- Specialization `s = t` from `ℤ[t,s]` to `ℤ[t]`. -/
noncomputable def specialize : Base →ₐ[ℤ] ℤ[X] := MvPolynomial.aeval fun _ => (X : ℤ[X])

/-- The Hankel determinant `d_m^{(k)}(n,t)`. -/
noncomputable def columnHankel (k m n : ℕ) : ℤ[X] :=
  (Matrix.of fun i j : Fin n => specialize (motzkin (m + i + j) k)).det

/-- `A_{k,r}(x,t)` of equation (1.28), a polynomial in `x` over `ℤ[t]`. -/
noncomputable def columnFactor (k r : ℕ) : (ℤ[X])[X] :=
  if r = 0 then 1 - C ((-1) ^ (k + 1).choose 2) * X ^ (k + 1)
  else 1 - C ((-1) ^ (k + 1).choose 2 * specialize (lucas r)) * X ^ (k + 1) + X ^ (2 * (k + 1))

/-- The denominator `∏_{j=0}^{⌊m/2⌋} A_{k,(k+1)(m-2j)}^{1+j(m-j)}` of equation (1.30). -/
noncomputable def columnDenominator (k m : ℕ) : (ℤ[X])[X] :=
  ∏ j ∈ Finset.range (m / 2 + 1), columnFactor k ((k + 1) * (m - 2 * j)) ^ (1 + j * (m - j))

/-- Conjecture 1.3. -/
def claim : Prop :=
  ∀ k m : ℕ, 1 ≤ m → ∃ R : (ℤ[X])[X],
    (R : PowerSeries ℤ[X]) =
        (columnDenominator k m : PowerSeries ℤ[X]) * PowerSeries.mk (columnHankel k m) ∧
      R.natDegree =
        (m + 1).choose 3 + k * (m.choose 1 + m.choose 2 + m.choose 3)

end D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinColumnDefs
