/- GID: D5/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/BarryRiordanPascalKernelDeterminant
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse, mathlib/module/Mathlib.RingTheory.PowerSeries.WellKnown, mathlib/module/Mathlib.LinearAlgebra.Matrix.Block]
   utility: none
   digest: Barry's Riordan kernel matrix is a Gram product with determinant one. -/

/- Formalization classification:
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #9215)
   Direct frozen dependencies: none (pinned Mathlib only)
-/


import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix

namespace D5.S1.Recurrence.Algebraic.BarryRiordanPascalKernelDeterminant

/-- The Riordan array `M^{(m)}(a,b) = (1/(1−ax), x(1+bx)/(1−ax)^m)` (page 1):
entry `T_{n,k} = [x^n] g(x) f(x)^k` (§2: the `k`-th column is generated
by `g f^k`, columns indexed from `0`). `1/(1−ax)` is the power-series inverse
`invOfUnit (1 - C a * X) 1`. -/
noncomputable def riordan (m : ℕ) (a b : ℤ) (n k : ℕ) : ℤ :=
  PowerSeries.coeff n
    (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X) 1 *
      (PowerSeries.X * (1 + PowerSeries.C b * PowerSeries.X) *
        (PowerSeries.invOfUnit (1 - PowerSeries.C a * PowerSeries.X) 1) ^ m) ^ k)

/-- `P_n(x; m, a, b) = Σ_{k=0}^{n} T_{n,k} x^k` (page 19). -/
noncomputable def P (m : ℕ) (a b : ℤ) (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (riordan m a b n k) * Polynomial.X ^ k

/-- `M_n^{(2)}(1,1)`: the first `n+1` rows and columns (page 20). -/
noncomputable def M (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i k => riordan 2 1 1 i k

/-- `D̃_n(2,1,1)`: the `(i,k)` entry is the coefficient of `x^i y^k` in
`Σ_{j=0}^{n} P_j(x; 2,1,1) P_j(y; 2,1,1)` (page 20; the bivariate polynomial
lives in `Polynomial (Polynomial ℤ)`, outer variable `x`, inner `y`). -/
noncomputable def Dtilde (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i k =>
    ((∑ j ∈ Finset.range (n + 1),
        (P 2 1 1 j).map Polynomial.C * Polynomial.C (P 2 1 1 j)).coeff i).coeff k

/-- Conjecture 32 as printed, at `(a,b) = (1,1)`. -/
def claim : Prop :=
  ∀ n : ℕ, Dtilde n = (M n)ᵀ * M n ∧ (Dtilde n).det = 1

/-- Conjecture 32 holds. -/
theorem result : claim := by
  unfold claim
  intro n
  have hA : Dtilde n = (M n)ᵀ * M n := by
    have hzero : ∀ r c : ℕ, r < c → riordan 2 1 1 r c = 0 := by
      intro r c h
      unfold riordan
      rw [mul_assoc
        (PowerSeries.X : PowerSeries ℤ)
        (1 + PowerSeries.C (1 : ℤ) * PowerSeries.X)
        (PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2)]
      rw [mul_pow]
      rw [show
        PowerSeries.invOfUnit
            (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
          (PowerSeries.X ^ c *
            ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
              PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ c) =
          PowerSeries.X ^ c *
            (PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
              ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
                PowerSeries.invOfUnit
                  (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ c) by
            ac_rfl]
      rw [PowerSeries.coeff_X_pow_mul']
      simp [Nat.not_le.mpr h]
    ext i k
    rw [Dtilde, Matrix.mul_apply]
    change
      ((∑ j ∈ Finset.range (n + 1),
          (P 2 1 1 j).map Polynomial.C * Polynomial.C (P 2 1 1 j)).coeff i.val).coeff k.val =
        ∑ j : Fin (n + 1), riordan 2 1 1 j.val i.val * riordan 2 1 1 j.val k.val
    rw [Fin.sum_univ_eq_sum_range
      (fun j => riordan 2 1 1 j i.val * riordan 2 1 1 j k.val) (n + 1)]
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
      Polynomial.coeff_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases hi : i.val ≤ j
    · by_cases hk : k.val ≤ j
      · simp [Finset.mem_range, hi, hk]
      · have hzero_k : riordan 2 1 1 j k.val = 0 :=
          hzero j k.val (Nat.lt_of_not_ge hk)
        simp [Finset.mem_range, hi, hk, hzero_k]
    · have hzero_i : riordan 2 1 1 j i.val = 0 :=
        hzero j i.val (Nat.lt_of_not_ge hi)
      simp [hi, hzero_i]
  have hB : (Dtilde n).det = 1 := by
    have hzero : ∀ r c : ℕ, r < c → riordan 2 1 1 r c = 0 := by
      intro r c h
      unfold riordan
      rw [mul_assoc
        (PowerSeries.X : PowerSeries ℤ)
        (1 + PowerSeries.C (1 : ℤ) * PowerSeries.X)
        (PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2)]
      rw [mul_pow]
      rw [show
        PowerSeries.invOfUnit
            (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
          (PowerSeries.X ^ c *
            ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
              PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ c) =
          PowerSeries.X ^ c *
            (PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
              ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
                PowerSeries.invOfUnit
                  (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ c) by
            ac_rfl]
      rw [PowerSeries.coeff_X_pow_mul']
      simp [Nat.not_le.mpr h]
    have hdiag : ∀ r : ℕ, riordan 2 1 1 r r = 1 := by
      intro r
      unfold riordan
      rw [mul_assoc
        (PowerSeries.X : PowerSeries ℤ)
        (1 + PowerSeries.C (1 : ℤ) * PowerSeries.X)
        (PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2)]
      rw [mul_pow]
      rw [show
        PowerSeries.invOfUnit
            (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
          (PowerSeries.X ^ r *
            ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
              PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ r) =
          PowerSeries.X ^ r *
            (PowerSeries.invOfUnit
                (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 *
              ((1 + PowerSeries.C (1 : ℤ) * PowerSeries.X) *
                PowerSeries.invOfUnit
                  (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 ^ 2) ^ r) by
            ac_rfl]
      rw [PowerSeries.coeff_X_pow_mul']
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hlower : (M n).IsLowerTriangular := by
      intro i j hij
      exact hzero i.val j.val hij
    have hdet : (M n).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular (M n) hlower]
      simp [M, hdiag]
    rw [hA, Matrix.det_mul, Matrix.det_transpose, hdet]
    norm_num
  exact ⟨hA, hB⟩

example : riordan 2 1 1 2 1 = 4 := by
  have hg :
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
        PowerSeries.invUnitsSub (1 : ℤˣ) := by
    have hi := PowerSeries.invOfUnit_mul
      (1 - PowerSeries.X : PowerSeries ℤ) 1 (by simp)
    have hj := PowerSeries.invUnitsSub_mul_sub (R := ℤ) (1 : ℤˣ)
    calc
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
          PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 * 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          ((1 - PowerSeries.X) * PowerSeries.invUnitsSub (1 : ℤˣ)) := by
            rw [show (1 - PowerSeries.X : PowerSeries ℤ) *
              PowerSeries.invUnitsSub (1 : ℤˣ) = 1 by simpa [mul_comm] using hj]
      _ = (PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          (1 - PowerSeries.X)) * PowerSeries.invUnitsSub (1 : ℤˣ) := by
            rw [mul_assoc]
      _ = PowerSeries.invUnitsSub (1 : ℤˣ) := by rw [hi, one_mul]
  rw [riordan, hg]
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_invUnitsSub, pow_two,
    PowerSeries.coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

example : riordan 2 1 1 3 2 = 7 := by
  have hg :
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
        PowerSeries.invUnitsSub (1 : ℤˣ) := by
    have hi := PowerSeries.invOfUnit_mul
      (1 - PowerSeries.X : PowerSeries ℤ) 1 (by simp)
    have hj := PowerSeries.invUnitsSub_mul_sub (R := ℤ) (1 : ℤˣ)
    calc
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
          PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 * 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          ((1 - PowerSeries.X) * PowerSeries.invUnitsSub (1 : ℤˣ)) := by
            rw [show (1 - PowerSeries.X : PowerSeries ℤ) *
              PowerSeries.invUnitsSub (1 : ℤˣ) = 1 by simpa [mul_comm] using hj]
      _ = (PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          (1 - PowerSeries.X)) * PowerSeries.invUnitsSub (1 : ℤˣ) := by
            rw [mul_assoc]
      _ = PowerSeries.invUnitsSub (1 : ℤˣ) := by rw [hi, one_mul]
  rw [riordan, hg]
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_invUnitsSub, pow_two,
    PowerSeries.coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

example : riordan 2 1 1 5 2 = 70 := by
  have hg :
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
        PowerSeries.invUnitsSub (1 : ℤˣ) := by
    have hi := PowerSeries.invOfUnit_mul
      (1 - PowerSeries.X : PowerSeries ℤ) 1 (by simp)
    have hj := PowerSeries.invUnitsSub_mul_sub (R := ℤ) (1 : ℤˣ)
    calc
      PowerSeries.invOfUnit
          (1 - PowerSeries.C (1 : ℤ) * PowerSeries.X) 1 =
          PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 * 1 := by simp
      _ = PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          ((1 - PowerSeries.X) * PowerSeries.invUnitsSub (1 : ℤˣ)) := by
            rw [show (1 - PowerSeries.X : PowerSeries ℤ) *
              PowerSeries.invUnitsSub (1 : ℤˣ) = 1 by simpa [mul_comm] using hj]
      _ = (PowerSeries.invOfUnit (1 - PowerSeries.X : PowerSeries ℤ) 1 *
          (1 - PowerSeries.X)) * PowerSeries.invUnitsSub (1 : ℤˣ) := by
            rw [mul_assoc]
      _ = PowerSeries.invUnitsSub (1 : ℤˣ) := by rw [hi, one_mul]
  rw [riordan, hg]
  norm_num [PowerSeries.coeff_mul, PowerSeries.coeff_invUnitsSub, pow_two,
    PowerSeries.coeff_X, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]

#print axioms result

end D5.S1.Recurrence.Algebraic.BarryRiordanPascalKernelDeterminant
