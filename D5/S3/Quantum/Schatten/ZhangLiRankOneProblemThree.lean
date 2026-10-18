/- GID: D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ZhangLiRankOneProblemThree
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: The rank-one unitarily invariant norm assertion of Zhang and Li Problem Three. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import D5.S3.Quantum.Schatten.ExpandingAverage
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Lattice

/-! The full rank-one assertion includes the finite permutation minimum, the
invertible-matrix product bound, and equality at the minimizing permutation. -/

noncomputable section
open Matrix
open scoped Matrix

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

/-- The finite permutation minimum is attained, with equal transpose-inverse factor. -/
theorem exists_minimizing_permutation (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ)
    (ν : UINorm n) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        ν.N ((σ.permMatrix ℂ) ⊙ G) ≤ ν.N ((τ.permMatrix ℂ) ⊙ G)) ∧
      ν.N ((σ.permMatrix ℂ) ⊙ G) * ν.N ((σ.permMatrix ℂ)⁻¹ ⊙ Gᵀ) =
        ν.N ((σ.permMatrix ℂ) ⊙ G) ^ 2 := by
  classical
  obtain ⟨σ, _, hσ⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun τ => ν.N ((τ.permMatrix ℂ) ⊙ G)) Finset.univ_nonempty
  refine ⟨σ, fun τ => hσ τ (Finset.mem_univ τ), ?_⟩
  rw [inverse_perm_hadamard_transpose, ν.N_transpose, pow_two]

end D5.S3.Quantum.Schatten.ZhangLiRankOneProblemThree
