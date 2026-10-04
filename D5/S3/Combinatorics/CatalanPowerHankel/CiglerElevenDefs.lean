/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerElevenDefs
   mirror-E: none(waiver:cigler-catalan-power-hankel-statement-definition)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Determinant.Basic, mathlib/module/Mathlib.Data.Nat.Choose.Basic, mathlib/module/Mathlib.Data.Rat.Defs]
   utility: none
   digest: Cigler's conjectured closed form for shifted Hankel determinants of odd Catalan powers. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenDefs

/-! Fixed public statement: J. Cigler, *Some experimental observations about Hankel
    determinants of convolution powers of Catalan numbers*, arXiv:2308.07642v2, (1), (2) and
    §2.2, Conjecture 11.  `C_{r,j} = r/(2j+r) · binom(2j+r, j)` for `j ≥ 0` and `C_{r,j} = 0`
    for `j < 0` are the coefficients of `c(x)^r`, `c` the Catalan generating function, and
    `D_{r,s}(N) = det (C_{r,i+j+s})_{0 ≤ i,j < N}` with `D_{r,s}(0) = 1`.  Conjecture 11: for
    `k ≥ 1`, `0 ≤ m ≤ k + 1` and `n ≥ 0`,
    `D_{2k+1, m-k+1}((2k+1) n + k) = (-1)^{k n + binom(k,2)} (2k+1)^m (n+1)^m`.
    The shift `m - k + 1` is an integer and may be negative. -/

/-- `C_{r,j}`: the coefficient of `x^j` in `c(x)^r`, zero for negative `j`. -/
def catalanPowerCoeff (r : ℕ) (j : ℤ) : ℚ :=
  if 0 ≤ j then
    (r : ℚ) / (2 * (j.toNat : ℚ) + r) * ((2 * j.toNat + r).choose j.toNat : ℚ)
  else 0

/-- `D_{r,s}(N) = det (C_{r,i+j+s})_{0 ≤ i,j < N}`. -/
def shiftedHankel (r : ℕ) (s : ℤ) (N : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin N => catalanPowerCoeff r ((i : ℤ) + j + s)).det

/-- Conjecture 11 for every `k ≥ 1`, `0 ≤ m ≤ k + 1` and `n ≥ 0`. -/
def claim : Prop :=
  ∀ k m n : ℕ, 1 ≤ k → m ≤ k + 1 →
    shiftedHankel (2 * k + 1) ((m : ℤ) - k + 1) ((2 * k + 1) * n + k) =
      (-1) ^ (k * n + k.choose 2) * ((2 * k + 1 : ℕ) : ℚ) ^ m * ((n + 1 : ℕ) : ℚ) ^ m

end D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenDefs
