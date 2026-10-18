/- GID: D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ZhangLiRankOneProblemThree
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: The rank-one unitarily invariant norm assertion of Zhang and Li Problem Three. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import D5.S3.Quantum.Schatten.ExpandingAverage
import D5.S3.Quantum.Schatten.RankOneHadamard
import D5.S3.Quantum.Schatten.ExpandingNormProduct
import D5.S3.Quantum.Schatten.ExpandingDiagonal
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The full rank-one assertion includes the finite permutation minimum, the
invertible-matrix product bound, and equality at the minimizing permutation. -/

noncomputable section
open Matrix
open scoped Matrix ComplexOrder

namespace D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree

def claim : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.rank ≤ 1 → ∀ ν : UINorm n,
    ∃ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        ν.N ((σ.permMatrix ℂ) ⊙ G) ≤ ν.N ((τ.permMatrix ℂ) ⊙ G)) ∧
      (∀ W : Matrix (Fin n) (Fin n) ℂ, IsUnit W.det →
        ν.N ((σ.permMatrix ℂ) ⊙ G) ^ 2 ≤ ν.N (W ⊙ G) * ν.N (W⁻¹ ⊙ Gᵀ)) ∧
      ν.N ((σ.permMatrix ℂ) ⊙ G) * ν.N ((σ.permMatrix ℂ)⁻¹ ⊙ Gᵀ) =
        ν.N ((σ.permMatrix ℂ) ⊙ G) ^ 2

private theorem inverse_perm_hadamard_transpose {n : ℕ} (σ : Equiv.Perm (Fin n))
    (G : Matrix (Fin n) (Fin n) ℂ) :
    (σ.permMatrix ℂ)⁻¹ ⊙ Gᵀ = (σ.permMatrix ℂ ⊙ G)ᵀ := by
  have hinv : (σ.permMatrix ℂ)⁻¹ = (σ.permMatrix ℂ)ᵀ := by
    apply Matrix.inv_eq_left_inv
    rw [transpose_permMatrix, ← permMatrix_mul]
    simp
  rw [hinv, transpose_hadamard]

/-- The rank-one assertion holds for every complex unitarily invariant norm. -/
theorem result : claim := by
  intro n G hG ν
  obtain ⟨a, b, ha, hb, hred⟩ := ν.rank_one_hadamard_reduction G hG
  obtain ⟨σ, hσ⟩ := ν.exists_permutation_expanding_lower_bound a b ha hb
  let A : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (a i : ℂ))
  let B : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (b i : ℂ))
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro τ
    rw [(hred (σ.permMatrix ℂ)).1, (hred (τ.permMatrix ℂ)).1]
    apply hσ
    have hP : (τ.permMatrix ℂ)ᴴ * τ.permMatrix ℂ = 1 := by
      rw [conjTranspose_permMatrix, ← permMatrix_mul]
      simp
    rw [hP, sub_self]
    exact PosSemidef.zero
  · intro W hW
    rw [(hred (σ.permMatrix ℂ)).1, (hred W).1, (hred W).2]
    exact ν.sq_le_product_of_expanding_lower_bound A B
      (ν.N (A * σ.permMatrix ℂ * B)) (ν.nonneg _) hσ W hW
  · rw [inverse_perm_hadamard_transpose, ν.N_transpose, pow_two]

end D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
