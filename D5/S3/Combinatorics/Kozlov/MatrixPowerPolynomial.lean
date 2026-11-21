/- GID: D5/S3/Combinatorics/Kozlov/MatrixPowerPolynomial
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Kozlov/MatrixPowerPolynomial
   mirror-E: none(waiver:finite-matrix-interpolation)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer]
   utility: none
   digest: Each entry of a nonnegative power of a unitriangular matrix is polynomial in the exponent. -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.RingTheory.Polynomial.Pochhammer

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Lattice/TransferEhrhart.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
When the project's pinned Mathlib provides an equivalent declaration,
replace the transplanted declaration with a direct import and use that result.

MIT License

Copyright (c) 2026 Jan Snellman

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

set_option autoImplicit false

open Finset Matrix Polynomial
open scoped BigOperators Polynomial

namespace D5.S3.Combinatorics.Kozlov

section Powers

variable {R : Type*} [CommSemiring R] {m : ℕ}

/-- The strictly-upper (off-diagonal) part of a matrix: `T` with its diagonal
replaced by `0`. For an upper unitriangular `T` this is `𝒩 = T − I`. -/
def offDiag (T : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => if i = j then 0 else T i j

theorem one_add_offDiag {T : Matrix (Fin m) (Fin m) R} (hdiag : ∀ i, T i i = 1) :
    1 + offDiag T = T := by
  ext i j
  by_cases h : i = j
  · subst h; simp [offDiag, hdiag]
  · simp [offDiag, h, Matrix.one_apply_ne h]

/-- Powers of a strictly upper triangular matrix: `(N^k) i j = 0` unless
`j ≥ i + k`. -/
theorem pow_apply_eq_zero {N : Matrix (Fin m) (Fin m) R}
    (hN : ∀ i j : Fin m, j ≤ i → N i j = 0) (k : ℕ) (i j : Fin m)
    (h : j.val < i.val + k) : (N ^ k) i j = 0 := by
  induction k generalizing j with
  | zero =>
    have : j ≠ i := fun e => by subst e; omega
    simp [Matrix.one_apply_ne' this]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l.val (i.val + k) with hl | hl
    · rw [ih l hl, zero_mul]
    · rw [hN l j (Fin.le_def.mpr (by omega)), mul_zero]

theorem pow_eq_zero_of_le {N : Matrix (Fin m) (Fin m) R}
    (hN : ∀ i j : Fin m, j ≤ i → N i j = 0) {k : ℕ} (hk : m ≤ k) : N ^ k = 0 := by
  ext i j
  exact pow_apply_eq_zero hN k i j (by have := j.isLt; omega)

/-- **Binomial expansion of a unitriangular power.** If `T` is upper
unitriangular of size `m`, then `T^k = ∑_{j<m} C(k,j) 𝒩^j` with `𝒩 = T − I`,
for every `k` (the terms `j ≥ m` vanish because `𝒩^m = 0`). -/
theorem pow_eq_sum_choose {T : Matrix (Fin m) (Fin m) R}
    (hlow : ∀ i j, j < i → T i j = 0) (hdiag : ∀ i, T i i = 1) (k : ℕ) :
    T ^ k = ∑ j ∈ range m, (k.choose j : R) • offDiag T ^ j := by
  have hN : ∀ i j : Fin m, j ≤ i → offDiag T i j = 0 := by
    intro i j hji
    rcases eq_or_lt_of_le hji with h | h
    · simp [offDiag, h]
    · simp [offDiag, hlow i j h, (ne_of_lt h).symm]
  have hc : Commute (offDiag T) (1 : Matrix (Fin m) (Fin m) R) := Commute.one_right _
  have hT : T ^ k = (offDiag T + 1) ^ k := by rw [add_comm, one_add_offDiag hdiag]
  rw [hT, hc.add_pow]
  have e : ∀ j, offDiag T ^ j * 1 ^ (k - j) * (k.choose j : Matrix (Fin m) (Fin m) R) =
      (k.choose j : R) • offDiag T ^ j := by
    intro j
    rw [one_pow, mul_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul']
  simp_rw [e]
  have hsub1 : range (k + 1) ⊆ range (k + 1 + m) := range_subset_range.mpr (by omega)
  have hsub2 : range m ⊆ range (k + 1 + m) := range_subset_range.mpr (by omega)
  rw [Finset.sum_subset hsub1, ← Finset.sum_subset hsub2]
  · intro j _ hjm
    simp only [mem_range, not_lt] at hjm
    rw [pow_eq_zero_of_le hN hjm, smul_zero]
  · intro j _ hjk
    simp only [mem_range, not_lt] at hjk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

end Powers

noncomputable def powerPolynomial {m : ℕ} (T : Matrix (Fin m) (Fin m) ℚ)
    (i j : Fin m) : ℚ[X] :=
  ∑ k ∈ range m, C ((offDiag T ^ k) i j / (k.factorial : ℚ)) * descPochhammer ℚ k

theorem powerPolynomial_eval {m : ℕ} {T : Matrix (Fin m) (Fin m) ℚ}
    (hlow : ∀ i j, j < i → T i j = 0) (hdiag : ∀ i, T i i = 1)
    (i j : Fin m) (r : ℕ) :
    (powerPolynomial T i j).eval (r : ℚ) = (T ^ r) i j := by
  rw [powerPolynomial, eval_finsetSum, pow_eq_sum_choose hlow hdiag, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp only [div_eq_mul_inv]
  ac_rfl

end D5.S3.Combinatorics.Kozlov
