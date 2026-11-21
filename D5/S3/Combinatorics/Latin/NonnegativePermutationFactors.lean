/- GID: D5/S3/Combinatorics/Latin/NonnegativePermutationFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Latin/NonnegativePermutationFactors
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   utility: none
   digest: If a product of square nonnegative integer matrices is a permutation matrix, every factor is one. -/

/-
admission_basis: escape-witness (the-omega-institute/trureturing-requests#196)
escape_witness: left_inverse_perm (a nonnegative integer matrix A with a nonnegative integer
  matrix C satisfying A * C = 1 is a permutation matrix: each column k of C A = 1 has a
  positive diagonal term C k (g k) * A (g k) k, the off-diagonal zeros of A C force column k of
  A to be supported at g k only, the diagonal of C A then gives A (g k) k = 1, and the diagonal
  of A C makes g surjective, hence a bijection).
proof_shape:
  IsPermMatrix, claim: source definitions; consumer: result.
  permMatrix_entry: bind-only helper (definitional unfolding); consumer: left_inverse_perm.
  left_inverse_perm: content; consumer: pair_perm.
  pair_perm: bind-only helper (A * B = P gives A * (B * P⁻¹) = 1 and B * (P⁻¹ * A) = 1 by
    permMatrix algebra and mul_eq_one_comm, then left_inverse_perm); consumer: result.
  result: content (induction on the list of factors).
Direct frozen dependencies: none (Mathlib only).
Search record (§3.1): Mathlib/LinearAlgebra/Matrix/Permutation.lean, Stochastic.lean,
  Analysis/Convex/DoublyStochasticMatrix.lean and Birkhoff.lean have permMatrix algebra and
  stochasticity, but no characterization of permutation matrices as nonnegative matrices with a
  nonnegative inverse; D5/S3/Combinatorics/Latin/ClassicalPerfectTensorFactorization proves the
  classical factorization theorem by orthogonal arrays and has no matrix statement. Mathlib
  supplies Equiv.Perm.permMatrix, Matrix.permMatrix_mul, Matrix.permMatrix_one and
  mul_eq_one_comm (Dedekind-finiteness of square matrices).
-/

import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.Mul

/-! # Nonnegative integer factors of a permutation matrix

A nonnegative integer matrix is modelled as a matrix over `ℕ`. If `A * C = 1` over `ℕ`, then
`C * A = 1` as well, and nonnegativity forces every column of `A` to contain exactly one entry
`1` and zeros elsewhere, at distinct rows; hence `A` is a permutation matrix. For a product of
two factors equal to a permutation matrix `P`, multiplying by `P⁻¹` on the appropriate side
returns to this case for each factor, and induction on the list of factors covers products of
any length, including the empty product and size zero.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Latin.NonnegativePermutationFactors

open Matrix

/-- A square matrix over `ℕ` is a permutation matrix. -/
def IsPermMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), M = σ.permMatrix ℕ

/-- Every factor of a product of nonnegative integer `n × n` matrices that equals a permutation
matrix is itself a permutation matrix. -/
def claim : Prop :=
  ∀ (n : ℕ) (L : List (Matrix (Fin n) (Fin n) ℕ)), IsPermMatrix L.prod → ∀ A ∈ L, IsPermMatrix A

private theorem permMatrix_entry {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    σ.permMatrix ℕ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- A nonnegative integer matrix with a nonnegative integer right inverse is a permutation
matrix. -/
private theorem left_inverse_perm {n : ℕ} {A C : Matrix (Fin n) (Fin n) ℕ} (h : A * C = 1) :
    IsPermMatrix A := by
  have h' := mul_eq_one_comm.mp h
  have hAC : ∀ i j, ∑ k, A i k * C k j = if i = j then 1 else 0 := fun i j => by
    rw [← Matrix.mul_apply, h, Matrix.one_apply]
  have hCA : ∀ k, ∑ i, C k i * A i k = 1 := fun k => by
    rw [← Matrix.mul_apply, h', Matrix.one_apply_eq]
  have hex : ∀ k, ∃ i, 0 < C k i * A i k := fun k => by
    by_contra hk
    push Not at hk
    have := hCA k
    rw [Finset.sum_eq_zero (fun i _ => Nat.le_zero.mp (hk i))] at this
    exact absurd this (by norm_num)
  choose g hg using hex
  have hsupp : ∀ i k, 0 < A i k → i = g k := fun i k hik => by
    by_contra hne
    have h0 : ∑ k', A i k' * C k' (g k) = 0 := by rw [hAC]; simp [hne]
    have hle := Finset.single_le_sum (f := fun k' => A i k' * C k' (g k))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hCk : 0 < C k (g k) := Nat.pos_of_mul_pos_right (hg k)
    have : 0 < A i k * C k (g k) := Nat.mul_pos hik hCk
    omega
  have hone : ∀ k, A (g k) k = 1 := fun k => by
    have hs := hCA k
    rw [Finset.sum_eq_single (g k)] at hs
    · exact Nat.eq_one_of_mul_eq_one_left hs
    · intro i _ hi
      have : A i k = 0 := by
        by_contra hne
        exact hi (hsupp i k (Nat.pos_of_ne_zero hne))
      simp [this]
    · simp
  have hentry : ∀ i k, A i k = if g k = i then 1 else 0 := fun i k => by
    split_ifs with hgi
    · rw [← hgi]; exact hone k
    · by_contra hne
      exact hgi (hsupp i k (Nat.pos_of_ne_zero hne)).symm
  have hsurj : Function.Surjective g := fun i => by
    have hs := hAC i i
    simp only [↓reduceIte] at hs
    obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.univ, A i k * C k i ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [Finset.sum_eq_zero hc] at hs
      exact absurd hs (by norm_num)
    exact ⟨k, (hsupp i k (Nat.pos_of_ne_zero (left_ne_zero_of_mul hk))).symm⟩
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective g ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  refine ⟨e.symm, ?_⟩
  ext i k
  rw [permMatrix_entry, hentry]
  have : (g k = i) ↔ (e.symm i = k) := by
    rw [Equiv.symm_apply_eq]; exact eq_comm
  simp only [this]

/-- If a product of two nonnegative integer matrices is a permutation matrix, both factors are
permutation matrices. -/
private theorem pair_perm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℕ} (σ : Equiv.Perm (Fin n))
    (h : A * B = σ.permMatrix ℕ) : IsPermMatrix A ∧ IsPermMatrix B := by
  have hinv1 : σ.permMatrix ℕ * σ⁻¹.permMatrix ℕ = 1 := by
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  have hinv2 : σ⁻¹.permMatrix ℕ * σ.permMatrix ℕ = 1 := by
    rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  refine ⟨left_inverse_perm (C := B * σ⁻¹.permMatrix ℕ) ?_, ?_⟩
  · rw [← Matrix.mul_assoc, h, hinv1]
  · refine left_inverse_perm (C := σ⁻¹.permMatrix ℕ * A) (mul_eq_one_comm.mp ?_)
    rw [Matrix.mul_assoc, h, hinv2]

/-- The claim holds for every size `n` and every finite list of factors. -/
theorem result : claim := by
  intro n L
  induction L with
  | nil => intro _ A hA; simp at hA
  | cons B L ih =>
    rintro ⟨σ, hσ⟩ A hA
    rw [List.prod_cons] at hσ
    obtain ⟨hB, hL⟩ := pair_perm σ hσ
    rcases List.mem_cons.mp hA with rfl | hA
    · exact hB
    · exact ih hL A hA

end D5.S3.Combinatorics.Latin.NonnegativePermutationFactors
