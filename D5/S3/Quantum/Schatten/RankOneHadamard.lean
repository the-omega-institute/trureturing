/- GID: D5/S3/Quantum/Schatten/RankOneHadamard
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/RankOneHadamard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rank-one Schur multipliers reduce to nonnegative diagonal products. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! Rank-one factorization, phase removal and transpose reduction of Schur products. -/

noncomputable section
open Matrix

namespace D5.S3.Quantum.Schatten

/-- A matrix of rank at most one is an outer product, including in dimension zero. -/
theorem exists_rank_one_factors {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.rank ≤ 1) : ∃ x y : Fin n → ℂ, G = vecMulVec x y := by
  classical
  obtain ⟨x, hx⟩ := (finrank_le_one_iff (K := ℂ)
    (V := LinearMap.range G.mulVecLin)).mp hG
  have hcol (j : Fin n) : G.col j ∈ LinearMap.range G.mulVecLin := by
    refine ⟨Pi.single j 1, ?_⟩
    exact G.mulVec_single_one j
  choose y hy using fun j => hx ⟨G.col j, hcol j⟩
  refine ⟨x.val, y, ?_⟩
  ext i j
  have h := congrArg (fun z : LinearMap.range G.mulVecLin => z.val i) (hy j)
  simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    vecMulVec_apply, mul_comm] using h.symm

private def scalarPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

private theorem scalarPhase_mul_norm (z : ℂ) : scalarPhase z * (‖z‖ : ℂ) = z := by
  by_cases hz : z = 0
  · simp [scalarPhase, hz]
  · simp [scalarPhase, hz, Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]

private theorem scalarPhase_mul_conj (z : ℂ) : scalarPhase z * star (scalarPhase z) = 1 := by
  have hn : ‖scalarPhase z‖ = 1 := by
    by_cases hz : z = 0
    · simp [scalarPhase, hz]
    · simp [scalarPhase, hz, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), norm_ne_zero_iff.mpr hz]
  simpa only [RCLike.star_def, hn, Complex.ofReal_one, one_pow] using
    Complex.mul_conj' (scalarPhase z)

private theorem diagonal_scalarPhase_unitary {n : ℕ} (x : Fin n → ℂ) :
    diagonal (fun i => scalarPhase (x i)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff]
  change diagonal (fun i => scalarPhase (x i)) *
    (diagonal (fun i => scalarPhase (x i)))ᴴ = 1
  simp only [diagonal_conjTranspose, diagonal_mul_diagonal, Pi.star_apply]
  simpa only [scalarPhase_mul_conj] using (diagonal_one :
    diagonal (fun _ : Fin n => (1 : ℂ)) = 1)

private theorem diagonal_mul_hadamard {n : ℕ} (x y : Fin n → ℂ)
    (W : Matrix (Fin n) (Fin n) ℂ) :
    diagonal x * W * diagonal y = W ⊙ vecMulVec x y := by
  ext i j
  simp only [mul_diagonal, diagonal_mul, hadamard_apply, vecMulVec_apply]
  ring

private theorem N_diagonal_remove_phases {n : ℕ} (ν : UINorm n)
    (x y : Fin n → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    ν.N (diagonal x * W * diagonal y) =
      ν.N (diagonal (fun i => (‖x i‖ : ℂ)) * W *
        diagonal (fun i => (‖y i‖ : ℂ))) := by
  have hprod : diagonal x * W * diagonal y =
      diagonal (fun i => scalarPhase (x i)) *
        (diagonal (fun i => (‖x i‖ : ℂ)) * W *
          diagonal (fun i => (‖y i‖ : ℂ))) *
        diagonal (fun i => scalarPhase (y i)) := by
    ext i j
    simp only [mul_diagonal, diagonal_mul]
    calc
      x i * W i j * y j = (scalarPhase (x i) * (‖x i‖ : ℂ)) * W i j *
          (scalarPhase (y j) * (‖y j‖ : ℂ)) := by rw [scalarPhase_mul_norm,
            scalarPhase_mul_norm]
      _ = _ := by ring
  rw [hprod]
  exact ν.unitary_invariant _ _ _ (diagonal_scalarPhase_unitary x)
    (diagonal_scalarPhase_unitary y)

private theorem N_real_diagonal_transpose {n : ℕ} (ν : UINorm n)
    (a b : Fin n → ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    ν.N (diagonal (fun i => (a i : ℂ)) * Zᵀ * diagonal (fun i => (b i : ℂ))) =
      ν.N (diagonal (fun i => (a i : ℂ)) * Zᴴ * diagonal (fun i => (b i : ℂ))) := by
  calc
    _ = ν.N ((diagonal (fun i => (a i : ℂ)) * Zᵀ *
        diagonal (fun i => (b i : ℂ)))ᵀ) := (ν.N_transpose _).symm
    _ = ν.N (diagonal (fun i => (b i : ℂ)) * Z *
        diagonal (fun i => (a i : ℂ))) := by simp [transpose_mul, Matrix.mul_assoc]
    _ = ν.N ((diagonal (fun i => (b i : ℂ)) * Z *
        diagonal (fun i => (a i : ℂ)))ᴴ) := (ν.N_conjTranspose _).symm
    _ = _ := by simp [conjTranspose_mul, Matrix.mul_assoc, Pi.star_def, RCLike.star_def]

namespace UINorm

/-- Both rank-one Schur factors are diagonal products with the same nonnegative weights. -/
theorem rank_one_hadamard_reduction {n : ℕ} (ν : UINorm n)
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.rank ≤ 1) :
    ∃ a b : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      ∀ W : Matrix (Fin n) (Fin n) ℂ,
        ν.N (W ⊙ G) = ν.N (diagonal (fun i => (a i : ℂ)) * W *
          diagonal (fun i => (b i : ℂ))) ∧
        ν.N (W⁻¹ ⊙ Gᵀ) = ν.N (diagonal (fun i => (a i : ℂ)) * (W⁻¹)ᴴ *
          diagonal (fun i => (b i : ℂ))) := by
  obtain ⟨x, y, rfl⟩ := exists_rank_one_factors G hG
  refine ⟨fun i => ‖x i‖, fun i => ‖y i‖, fun i => norm_nonneg _,
    fun i => norm_nonneg _, fun W => ⟨?_, ?_⟩⟩
  · rw [← diagonal_mul_hadamard]
    exact N_diagonal_remove_phases ν x y W
  · rw [← ν.N_transpose (W⁻¹ ⊙ (vecMulVec x y)ᵀ), transpose_hadamard,
      transpose_transpose, ← diagonal_mul_hadamard]
    exact (N_diagonal_remove_phases ν x y (W⁻¹)ᵀ).trans
      (N_real_diagonal_transpose ν (fun i => ‖x i‖) (fun i => ‖y i‖) W⁻¹)

end UINorm
end D5.S3.Quantum.Schatten
