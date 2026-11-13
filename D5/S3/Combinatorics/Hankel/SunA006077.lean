/- GID: D5/S3/Combinatorics/Hankel/SunA006077
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hankel/SunA006077
   mirror-E: none(waiver:symbolic-hankel-identities)
   anchors: []
   utility: none
   digest: The literal Sun finite sum and its sparse Hankel moment transform. -/

import Mathlib.Tactic

/-! Integer moments and finite polynomial translation for Sun's Hankel determinants. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Hankel.SunA006077

open Finset Polynomial

/-- The integral multinomial coefficient `(3r)!/(r!)^3`. -/
def c (r : ℕ) : ℤ := (Nat.choose (2*r) r : ℤ) * (Nat.choose (3*r) r : ℤ)

/-- Sun's literal finite sum; the summation bound ensures `3k ≤ n`. -/
def w (n : ℕ) : ℤ := ∑ k ∈ range (n / 3 + 1),
  (-1 : ℤ)^k * 3^(n-3*k) * (Nat.choose n (3*k) : ℤ) *
    (Nat.choose (2*k) k : ℤ) * (Nat.choose (3*k) k : ℤ)

/-- The determinant has rows and columns numbered from zero through `n`. -/
def W (n : ℕ) : ℤ := (Matrix.of fun i j : Fin (n+1) => w (i.val+j.val)).det

/-- The sparse moments before translation by three. -/
def sparse (n : ℕ) : ℤ := if n % 3 = 0 then (-1 : ℤ)^(n/3) * c (n/3) else 0

/-- Weighted binomial translation of integral moments. -/
def translate (x : ℤ) (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), x^(n-k) * (Nat.choose n k : ℤ) * b k

/-- The literal source sum is the binomial translation of the sparse moments. -/
theorem source_as_translate (n : ℕ) : w n = translate 3 sparse n := by
  classical
  unfold w translate sparse
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter]
  apply sum_bij (fun k _ => 3*k)
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_filter, mem_range]
    constructor
    · omega
    · omega
  · intro k _ l _ h
    omega
  · intro k hk
    simp only [mem_filter, mem_range] at hk
    refine ⟨k/3, mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    simp [c]
    ring

/-- Binomial translation preserves every finite Hankel determinant. -/
theorem translate_hankel_det (x : ℤ) (b : ℕ → ℤ) (N : ℕ) :
    (Matrix.of fun i j : Fin N => translate x b (i.val+j.val)).det =
      (Matrix.of fun i j : Fin N => b (i.val+j.val)).det := by
  classical
  let L : ℤ[X] →ₗ[ℤ] ℤ :=
    { toFun := fun p => p.sum fun r z => z * b r
      map_add' := by
        intro p q
        exact Polynomial.sum_add_index p q _ (by simp) (by intros; ring)
      map_smul' := by
        intro z p
        change (z • p).sum (fun r a => a * b r) = z * p.sum (fun r a => a * b r)
        rw [Polynomial.sum_smul_index' _ _ _ (by simp)]
        simp [← Finset.mul_sum, Polynomial.sum, mul_assoc] }
  have mono (r : ℕ) (z : ℤ) : L (monomial r z) = z * b r := by
    simp [L, Polynomial.sum_monomial_index]
  have power (r : ℕ) : L (X^r) = b r := by
    simpa only [monomial_one_right_eq_X_pow, one_mul] using mono r 1
  have expansion (r : ℕ) : L ((X + C x)^r) = translate x b r := by
    change (((X + C x)^r : ℤ[X]).sum fun k z => z * b k) = _
    rw [Polynomial.sum_over_range' _ (by simp) (r+1)]
    · simp only [coeff_X_add_C_pow, translate, mul_assoc]
    · simpa only [natDegree_pow, natDegree_X_add_C, mul_one] using Nat.lt_succ_self r
  let P : Matrix (Fin N) (Fin N) ℤ :=
    Matrix.of fun i j => ((X+C x)^i.val : ℤ[X]).coeff j.val
  have row (i : Fin N) :
      (∑ j : Fin N, (P i j) • (X^j.val : ℤ[X])) = (X+C x)^i.val := by
    have hdeg : ((X+C x)^i.val : ℤ[X]).degree < N := by
      rw [degree_pow, degree_X_add_C]
      simpa using i.isLt
    simpa [P, ← C_mul_X_pow_eq_monomial, smul_eq_C_mul] using
      (Polynomial.sum_fin (fun j z => monomial j z) (by simp) hdeg).trans
        (Polynomial.sum_monomial_eq _)
  have matrix_eq :
      (Matrix.of fun i j : Fin N => translate x b (i.val+j.val)) =
        P * (Matrix.of fun i j : Fin N => b (i.val+j.val)) * P.transpose := by
    ext i j
    simp only [Matrix.of_apply]
    rw [← expansion, pow_add, ← row i, ← row j]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_smul_comm,
      map_smul, ← pow_add, power, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, smul_eq_mul]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro d _
    ring
  have detP : P.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular P]
    · apply prod_eq_one
      intro i _
      change ((X+C x)^i.val : ℤ[X]).coeff i.val = 1
      rw [coeff_X_add_C_pow]
      simp
    · intro i j hij
      simp only [P, Matrix.of_apply, coeff_X_add_C_pow]
      rw [Nat.choose_eq_zero_of_lt (show i.val < j.val from hij), Int.natCast_zero, mul_zero]
  rw [matrix_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, detP, one_mul,
    mul_one]

/-- The source determinant equals the determinant of the sparse integer moments. -/
theorem source_hankel_reduction (n : ℕ) : W n =
    (Matrix.of fun i j : Fin (n+1) => sparse (i.val+j.val)).det := by
  unfold W
  simp_rw [source_as_translate]
  exact translate_hankel_det 3 sparse (n+1)

end D5.S3.Combinatorics.Hankel.SunA006077
