/- GID: D5/S3/Quantum/Schatten/ProductLogMajorization
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ProductLogMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horn weak log-majorization for arbitrary complex matrix products. -/

/-
Attributed source: leanprover-community/physlib, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Original module: QuantumInfo/ForMathlib/Majorization.lean.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Retire this transplant when an equivalent consumed declaration exists in the
repository-pinned Mathlib, replacing it by direct application.
No mathematical originality is claimed for the attributed source.
-/
module

public import D5.S3.Quantum.Schatten.CompoundMatrices

@[expose] public section

open Finset BigOperators Matrix
open scoped AllOrdered
variable {d : Type*} [Fintype d] [DecidableEq d]
noncomputable section

/- All eigenvalues of `A† A` are bounded by (max singular value)². -/
lemma eigenvalue_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (i : e) :
  (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 := by
  -- By definition of singular values, we know that $\sigma_i(A)^2 = \lambda_i(A^*A)$.
  have h_singular_value_squared : ∀ i, (singularValues A i) ^ 2 = (isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i := by
    intro i
    simp [singularValues]
    rw [Real.sq_sqrt (_)]
    convert Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i using 1
  rw [← h_singular_value_squared i]
  gcongr
  · exact Real.sqrt_nonneg _
  · convert singularValuesSorted_zero_eq_sup A h |> fun h => h.ge.trans' _
    exact Finset.le_sup' (fun i => singularValues A i) (Finset.mem_univ i)

/-- The quadratic form of `A† A` is bounded by (max singular value)² * ‖v‖². -/
lemma quadratic_form_le_singularValuesSorted_sq {e : Type*} [Fintype e] [DecidableEq e]
    (A : Matrix e e ℂ) (h : 0 < Fintype.card e) (v : e → ℂ) :
  Complex.re (star v ⬝ᵥ (A.conjTranspose * A).mulVec v) ≤
    (singularValuesSorted A ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
  apply le_trans (IsHermitian.inner_le_sup_eigenvalue_mul_inner (Aᴴ * A) (by
    simp [Matrix.IsHermitian]) h v)
  apply_rules [mul_le_mul_of_nonneg_right, Finset.sup'_le]
  · intro i _
    convert! eigenvalue_le_singularValuesSorted_sq A h i using 1
    simp [Matrix.conjTranspose_conjTranspose]
  · simp [dotProduct]
    exact Finset.sum_nonneg fun _ _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- The largest singular value of a matrix product is at most the product of the
largest singular values: `σ₁(M * N) ≤ σ₁(M) * σ₁(N)`.
This is operator-norm submultiplicativity. -/
lemma singularValuesSorted_mul_le {e : Type*} [Fintype e] [DecidableEq e]
    (M N : Matrix e e ℂ) (h : 0 < Fintype.card e) :
    singularValuesSorted (M * N) ⟨0, h⟩ ≤
    singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN).
  have h_eigenvalue_le : ∀ i, (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := by
    intro i
    have h_eigenvalue_le : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 := by
      -- By the properties of singular values and eigenvalues, we know that the eigenvalues of $(MN)^* (MN)$ are bounded by the product of the squares of the singular values of $M$ and $N$.
      have h_eigenvalue_bound : ∀ (v : e → ℂ), Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
        intro v
        have h_quadratic_form : Complex.re (star v ⬝ᵥ ((M * N).conjTranspose * (M * N)).mulVec v) ≤ (singularValuesSorted M ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) := by
          have := quadratic_form_le_singularValuesSorted_sq M h (N.mulVec v)
          convert this using 1 <;> simp [Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
        have h_quadratic_form_N : Complex.re (star v ⬝ᵥ (N.conjTranspose * N).mulVec v) ≤ (singularValuesSorted N ⟨0, h⟩) ^ 2 * Complex.re (star v ⬝ᵥ v) := by
          convert quadratic_form_le_singularValuesSorted_sq N h v using 1
        simpa only [mul_assoc] using h_quadratic_form.trans (mul_le_mul_of_nonneg_left h_quadratic_form_N (sq_nonneg _))
      convert h_eigenvalue_bound ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis i) using 1
      · have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues_eq i; aesop
      · simp [dotProduct]
        have := (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvectorBasis.orthonormal
        rw [orthonormal_iff_ite] at this
        simp_all [Complex.ext_iff, inner]
    linarith
  -- Apply the inequality eigenvalue_le_singularValuesSorted_sq to each eigenvalue of (MN)†(MN) and take the square root.
  have h_sqrt_eigenvalue_le : ∀ i, singularValues (M * N) i ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
    intro i
    have h_sqrt_eigenvalue_le_i : (isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i ≤ (singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩) ^ 2 := h_eigenvalue_le i
    have h_sqrt_eigenvalue_le_i' : Real.sqrt ((isHermitian_mul_conjTranspose_self (M * N).conjTranspose).eigenvalues i) ≤ singularValuesSorted M ⟨0, h⟩ * singularValuesSorted N ⟨0, h⟩ := by
      exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (singularValuesSorted_nonneg M ⟨0, h⟩) (singularValuesSorted_nonneg N ⟨0, h⟩), h_sqrt_eigenvalue_le_i⟩
    exact h_sqrt_eigenvalue_le_i' |> le_trans (by
    exact le_rfl)
  simp_all [Finset.sup'_le_iff]
  convert h_sqrt_eigenvalue_le using 1
  rw [singularValuesSorted_zero_eq_sup, singularValuesSorted_zero_eq_sup]

/-- Horn's inequality (weak log-majorization of singular values):
For all `k`, `∏_{i<k} σ↓ᵢ(AB) ≤ ∏_{i<k} σ↓ᵢ(A) · σ↓ᵢ(B)`.
This follows from submultiplicativity of the operator norm applied to
exterior powers of the matrices. -/
lemma horn_weak_log_majorization (A B : Matrix d d ℂ) (k : ℕ)
    (hk : k ≤ Fintype.card d) :
    ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩ ≤
    ∏ i : Fin k, (singularValuesSorted A ⟨i.val, by omega⟩ *
                   singularValuesSorted B ⟨i.val, by omega⟩) := by
  -- Rewrite the RHS as (prod of σ↓(A)) * (prod of σ↓(B))
  rw [Finset.prod_mul_distrib]
  -- Use the compound matrix characterisation and submultiplicativity
  have hcard : 0 < Fintype.card {S : Finset d // S.card = k} := by
    have : Fintype.card {S : Finset d // S.card = k} = (Fintype.card d).choose k := by
      simp [Fintype.card_subtype]
    rw [this]; exact Nat.choose_pos hk
  calc ∏ i : Fin k, singularValuesSorted (A * B) ⟨i.val, by omega⟩
      = singularValuesSorted (compoundMatrix (A * B) k) ⟨0, hcard⟩ :=
        prod_singularValuesSorted_eq_compoundSV (A * B) k hk
    _ = singularValuesSorted (compoundMatrix A k * compoundMatrix B k) ⟨0, hcard⟩ := by
        rw [compoundMatrix_mul]
    _ ≤ singularValuesSorted (compoundMatrix A k) ⟨0, hcard⟩ *
        singularValuesSorted (compoundMatrix B k) ⟨0, hcard⟩ :=
        singularValuesSorted_mul_le _ _ hcard
    _ = (∏ i : Fin k, singularValuesSorted A ⟨i.val, by omega⟩) *
        (∏ i : Fin k, singularValuesSorted B ⟨i.val, by omega⟩) := by
        rw [← prod_singularValuesSorted_eq_compoundSV A k hk,
            ← prod_singularValuesSorted_eq_compoundSV B k hk]


end
