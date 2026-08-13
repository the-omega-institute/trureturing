/- GID: D5/S3/Resource/CompositeConeDuality
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Hilbert-Schmidt duality between separable and block-positive matrix cones. -/

import Mathlib
import D5.S3.Resource.CompositeCones

/- Provenance: Native proof over pinned mathlib. -/
/- Search receipt (2026-08-13): searched D5 declarations and pinned mathlib for
   `blockPositive`, `separableCone`, matrix PSD self-duality, and cone-duality
   theorems. The exact local definitions/inclusions are in CompositeCones; the
   exact PSD finite rank-one decomposition is
   `Matrix.posSemidef_iff_eq_sum_vecMulVec` (Analysis/InnerProductSpace/Positive).
   `ProperCone.innerDual_innerDual` and `ProperCone.dual_flip_dual` were also
   found, but are not needed after the finite-dimensional decomposition. -/

namespace D5.S3.Resource.CompositeConeDuality

open D5.S3.Resource.CompositeCones
open scoped Kronecker
open scoped ComplexOrder

variable {m n : ℕ}

abbrev CompositeMatrix (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

/-- The real Hilbert-Schmidt pairing, linear in the second matrix. -/
noncomputable def pairing (S W : CompositeMatrix m n) : ℝ :=
  RCLike.re (Matrix.trace (Matrix.conjTranspose S * W))

private lemma pairing_rank_one (W : CompositeMatrix m n) (x : Fin m × Fin n → ℂ) :
    pairing (Matrix.vecMulVec x (star x)) W =
      RCLike.re (dotProduct (star x) (Matrix.mulVec W x)) := by
  unfold pairing
  simp only [Matrix.conjTranspose_vecMulVec, star_star]
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simp [dotProduct_comm]

private lemma kronecker_rank_one (a : Fin m → ℂ) (b : Fin n → ℂ) :
    (Matrix.vecMulVec a (star a) ⊗ₖ Matrix.vecMulVec b (star b) : CompositeMatrix m n) =
      Matrix.vecMulVec (fun ij : Fin m × Fin n => a ij.1 * b ij.2)
        (star (fun ij : Fin m × Fin n => a ij.1 * b ij.2)) := by
  ext i j
  simp [Matrix.kroneckerMap, Matrix.vecMulVec_apply, star_mul]
  ring

private lemma kronecker_sum_sum
    {ka kb : ℕ}
    (A : Fin ka → Matrix (Fin m) (Fin m) ℂ)
    (B : Fin kb → Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, A i) ⊗ₖ (∑ j, B j) = ∑ i, ∑ j, A i ⊗ₖ B j := by
  ext i j
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]

private lemma pairing_sum (W : CompositeMatrix m n)
    {k : ℕ}
    (f : Fin k → CompositeMatrix m n) :
    pairing (∑ i, f i) W = ∑ i, pairing (f i) W := by
  unfold pairing
  rw [Matrix.conjTranspose_sum]
  have hm : (∑ i, Matrix.conjTranspose (f i)) * W =
      ∑ i, Matrix.conjTranspose (f i) * W := by
    ext x y
    simp only [Matrix.mul_apply, Matrix.sum_apply]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [hm, Matrix.trace_sum]
  simp only [map_sum]

private lemma pairing_kronecker_nonneg (hW : blockPositive W)
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ pairing (A ⊗ₖ B) W := by
  obtain ⟨ka, va, hva⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA)
  obtain ⟨kb, vb, hvb⟩ := (Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hB)
  rw [hva, hvb, kronecker_sum_sum]
  rw [pairing_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [pairing_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [kronecker_rank_one, pairing_rank_one]
  exact hW (va i) (vb j)

theorem blockPositive_iff_forall_separable_pairing_nonneg (W : CompositeMatrix m n) :
    blockPositive W ↔
      ∀ S : CompositeMatrix m n, separableCone S → 0 ≤ pairing S W := by
  constructor
  · intro hW S hS
    obtain ⟨k, A, B, hAB, rfl⟩ := hS
    rw [pairing_sum]
    apply Finset.sum_nonneg
    intro i hi
    exact pairing_kronecker_nonneg hW (hAB i).1 (hAB i).2
  · intro hS a b
    let x : Fin m × Fin n → ℂ := fun ij => a ij.1 * b ij.2
    have hsep : separableCone (Matrix.vecMulVec a (star a) ⊗ₖ
        Matrix.vecMulVec b (star b) : CompositeMatrix m n) := by
      refine ⟨1, fun _ => Matrix.vecMulVec a (star a), fun _ => Matrix.vecMulVec b (star b), ?_, ?_⟩
      · intro i
        simp [Matrix.posSemidef_vecMulVec_self_star]
      · simp [kronecker_rank_one]
    have hp := hS _ hsep
    rw [kronecker_rank_one, pairing_rank_one] at hp
    exact hp

end D5.S3.Resource.CompositeConeDuality
