/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripProductDefs
   mirror-E: none(waiver:fixed-narayana-strip-product-statement-definition)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Eval.Defs]
   utility: none
   digest: Cigler's product formula for Narayana strip series of heights 4m and 4m+1. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductDefs

open Polynomial D5.S3.Combinatorics.NarayanaStrip.CiglerStripExpansionDefs

/-! Fixed public statement: Cigler, *Some sequences and number triangles which are related to
    Narayana polynomials and to q-Narayana polynomials for q=-1*, arXiv:2608.03363v2, §4,
    Conjecture 2, equation (79): for `m ≥ 1` and `h ∈ {4m, 4m+1}`,
    `C^{(h)}(t², z²) = c^{(h)}(t, z) c^{(h)}(-t, -z)`, where
    `C^{(h)}(t, z) = ∑ₙ C_n^{(h)}(t) zⁿ` with `C_n^{(h)} = stripSum tauPlus h n` and `c^{(h)}`
    likewise with `tauMinus`.  The identity of
    formal power series in `z` is stated coefficientwise. -/

/-- The coefficient of `z^N` in `C^{(h)}(t², z²)`. -/
noncomputable def lhsCoeff (h N : ℕ) : ℤ[X] :=
  if N % 2 = 0 then (stripSum tauPlus h (N / 2)).comp (X ^ 2) else 0

/-- The coefficient of `z^N` in `c^{(h)}(t, z) c^{(h)}(-t, -z)`. -/
noncomputable def rhsCoeff (h N : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (N + 1),
    stripSum tauMinus h i * ((-1) ^ (N - i) * (stripSum tauMinus h (N - i)).comp (-X))

/-- Conjecture 2, equation (79): the factorization holds for heights `4m` and `4m + 1`, `m ≥ 1`. -/
def claim : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ,
    lhsCoeff (4 * m) N = rhsCoeff (4 * m) N ∧ lhsCoeff (4 * m + 1) N = rhsCoeff (4 * m + 1) N

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductDefs
