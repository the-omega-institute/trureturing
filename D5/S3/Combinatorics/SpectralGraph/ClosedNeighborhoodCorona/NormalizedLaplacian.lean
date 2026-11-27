/- GID: D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/NormalizedLaplacian
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized-Laplacian similarity under a block orthogonal lift.
-/

module

public import D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona.Blocks
public import D5.S3.Combinatorics.SpectralGraph.ClosedNeighborhoodCorona.RegularIntertwiner
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace ClosedNeighborhoodCorona

public section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inverse square-root degree, with the value at zero fixed to zero. -/
noncomputable def inverseSqrtDegree (G : SimpleGraph V) (v : V) : ℝ :=
  if G.degree v = 0 then 0 else (Real.sqrt (G.degree v : ℝ))⁻¹

/-- The diagonal inverse-square-root degree matrix. -/
noncomputable def degreeScale (G : SimpleGraph V) : Matrix V V ℝ :=
  diagonal (inverseSqrtDegree G)

/-- The normalized Laplacian, with isolated vertices contributing zero rows. -/
noncomputable def normalizedLaplacian (G : SimpleGraph V) : Matrix V V ℝ :=
  degreeScale G * (diagonal (fun v => (G.degree v : ℝ)) - G.adjMatrix ℝ) * degreeScale G

private theorem charpoly_of_orthogonal_intertwining
    {A B U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1)
    (h : U * A = B * U) : A.charpoly = B.charpoly := by
  apply Matrix.charpoly_eq_of_mul_eq_mul (P := Uᵀ)
  · have hd : Uᵀ.det * U.det = 1 := by
      rw [← det_mul, h₁, det_one]
    intro hz
    rw [hz, zero_mul] at hd
    exact zero_ne_one hd
  · rw [Matrix.mul_assoc A, ← Matrix.mul_assoc U, h, Matrix.mul_assoc B,
      ← transpose_mul, h₂, transpose_one, mul_one]

/-- A block-diagonal lift of an orthogonal map on the base and its copies. -/
noncomputable def blockLift (U : Matrix V V ℝ) (W : Type*) :
    Matrix (V ⊕ (V × W)) (V ⊕ (V × W)) ℝ :=
  fromBlocks U 0 0 (U ⊗ₖ (1 : Matrix W W ℝ))

private theorem blockLift_orthogonal {W : Type*} [Fintype W] [DecidableEq W]
    {U : Matrix V V ℝ} (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1) :
    (blockLift U W)ᵀ * blockLift U W = 1 ∧
      blockLift U W * (blockLift U W)ᵀ = 1 := by
  simp [blockLift, fromBlocks_transpose, fromBlocks_multiply, h₁, h₂,
    ← mul_kronecker_mul]

private theorem blockLift_adjacency
    {W : Type*} [Fintype W] [DecidableEq W]
    (G₁ G₂ : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ} (hU : U * G₁.adjMatrix ℝ = G₂.adjMatrix ℝ * U)
    (h₁ : Uᵀ * U = 1) :
    blockLift U W * (corona G₁ H).adjMatrix ℝ =
      (corona G₂ H).adjMatrix ℝ * blockLift U W := by
  rw [adjMatrix_corona, adjMatrix_corona]
  simp only [blockLift, fromBlocks_multiply, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, ← mul_kronecker_mul]
  · rw [hU]
  · rw [hU, transpose_mul, h₁, transpose_one, one_mul]

/- The following algebraic bridge isolates the only degree-scaling obligation.
It is stated for the registered matrices so that callers can discharge the
pointwise degree calculation, including the zero-degree branch, independently
of the characteristic-polynomial argument. -/
theorem normalized_laplacian_similarity_of_block
    {W : Type*} [Fintype W] [DecidableEq W]
    {G₁ G₂ : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] [DecidableRel H.Adj]
    {U : Matrix V V ℝ}
    (h₁ : Uᵀ * U = 1) (h₂ : U * Uᵀ = 1)
    (hScale : blockLift U W * degreeScale (corona G₁ H) =
      degreeScale (corona G₂ H) * blockLift U W)
    (hCore : blockLift U W *
      (diagonal (fun x => ((corona G₁ H).degree x : ℝ)) -
        (corona G₁ H).adjMatrix ℝ) =
      (diagonal (fun x => ((corona G₂ H).degree x : ℝ)) -
        (corona G₂ H).adjMatrix ℝ) * blockLift U W) :
    (normalizedLaplacian (corona G₁ H)).charpoly =
      (normalizedLaplacian (corona G₂ H)).charpoly := by
  apply charpoly_of_orthogonal_intertwining
  · exact blockLift_orthogonal h₁ h₂ |>.1
  · exact blockLift_orthogonal h₁ h₂ |>.2
  unfold normalizedLaplacian
  rw [Matrix.mul_assoc, hScale, ← Matrix.mul_assoc, hCore,
    Matrix.mul_assoc, ← hScale, Matrix.mul_assoc]

end

end ClosedNeighborhoodCorona
