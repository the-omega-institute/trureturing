/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ParityGreenDefect
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank]
   utility: none
   digest: The parity Green defect and its crossed blocks factor through crossing kernels. -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.LinearCombination

/-! The parity-specific Green identity for finite real crossing matrices. -/

@[expose] public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenDefect

open Matrix

/-- Data for one selected block. The types `e` and `o` index the selected parities.
The type `n` indexes the exterior parity opposite to `e`. -/
structure GreenBlock (e o n ι : Type*) [Fintype e] [DecidableEq e] [Fintype o]
    [Fintype n] [DecidableEq ι] where
  adjacency : Matrix e o ℝ
  crossing : Matrix e n ℝ
  size : ℝ
  evenPotential : ι → e → ℝ
  oddPotential : ι → o → ℝ
  evenSource : ι → e → ℝ
  oddSource : ι → o → ℝ
  exterior : ι → n → ℝ
  even_laplace : ∀ i,
    (3 : ℝ) • evenPotential i - adjacency *ᵥ oddPotential i = evenSource i
  odd_laplace : ∀ i,
    (3 : ℝ) • oddPotential i - adjacencyᵀ *ᵥ evenPotential i = oddSource i
  crossing_mul_transpose :
    crossing * crossingᵀ = (9 : ℝ) • 1 - adjacency * adjacencyᵀ
  crossing_exterior : ∀ i,
    crossing *ᵥ exterior i =
      (-1 / 3 : ℝ) • ((3 : ℝ) • evenSource i + adjacency *ᵥ oddSource i)
  exterior_gram : ∀ i j,
    exterior i ⬝ᵥ exterior j + (oddSource i ⬝ᵥ oddSource j) / 9 =
      size * ((if i = j then (1 : ℝ) else 0) - 1 / 9) / 2

namespace GreenBlock

variable {e o n ι : Type*} [Fintype e] [DecidableEq e] [Fintype o]
  [Fintype n] [DecidableEq ι]

/-- The row-space part of an exterior direction. -/
noncomputable def projected (B : GreenBlock e o n ι) (i : ι) : n → ℝ :=
  (-1 / 3 : ℝ) • (B.crossingᵀ *ᵥ B.evenPotential i)

/-- The part of an exterior direction left after projection. -/
noncomputable def residual (B : GreenBlock e o n ι) (i : ι) : n → ℝ :=
  B.exterior i - B.projected i

/-- The Green defect with the contributions of both selected parities. -/
noncomputable def defect (B : GreenBlock e o n ι) : Matrix ι ι ℝ :=
  of fun i j ↦ (B.size / 6) * (9 * (if i = j then (1 : ℝ) else 0) - 1) -
    (B.evenPotential i ⬝ᵥ B.evenSource j + B.oddPotential i ⬝ᵥ B.oddSource j)

private theorem dot_projected_eq_zero (B : GreenBlock e o n ι) (i : ι) (v : n → ℝ)
    (hv : B.crossing *ᵥ v = 0) : v ⬝ᵥ B.projected i = 0 := by
  rw [projected, dotProduct_smul, dotProduct_transpose_mulVec, hv, dotProduct_zero, smul_zero]

/-- The rectangular Laplace equations give a crossing-kernel residual and express the whole
Green defect as three times the dot product of these residuals on a single exterior parity. -/
theorem green_defect (B : GreenBlock e o n ι) :
    (∀ i, B.crossing *ᵥ B.residual i = 0) ∧
    (∀ i j, B.defect i j = 3 * (B.residual i ⬝ᵥ B.residual j)) := by
  have hOdd (i : ι) :
      B.adjacencyᵀ *ᵥ B.evenPotential i = (3 : ℝ) • B.oddPotential i - B.oddSource i := by
    rw [← B.odd_laplace i]
    abel
  have hElim (i : ι) :
      (B.crossing * B.crossingᵀ) *ᵥ B.evenPotential i =
        (3 : ℝ) • B.evenSource i + B.adjacency *ᵥ B.oddSource i := by
    rw [B.crossing_mul_transpose, sub_mulVec, smul_mulVec, one_mulVec, ← mulVec_mulVec,
      hOdd, mulVec_sub, mulVec_smul, ← B.even_laplace i]
    ext a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hCross (i : ι) : B.crossing *ᵥ B.projected i = B.crossing *ᵥ B.exterior i := by
    rw [projected, mulVec_smul, mulVec_mulVec, hElim, B.crossing_exterior]
  have hKer (i : ι) : B.crossing *ᵥ B.residual i = 0 := by
    rw [residual, mulVec_sub, hCross, sub_self]
  have hProjected (i j : ι) :
      B.projected i ⬝ᵥ B.projected j =
        (B.evenPotential i ⬝ᵥ B.evenSource j + B.oddPotential i ⬝ᵥ B.oddSource j) / 3 -
          (B.oddSource i ⬝ᵥ B.oddSource j) / 9 := by
    rw [dotProduct_comm (B.projected i) (B.projected j)]
    change B.projected j ⬝ᵥ ((-1 / 3 : ℝ) • (B.crossingᵀ *ᵥ B.evenPotential i)) = _
    rw [dotProduct_smul, dotProduct_transpose_mulVec,
      hCross, B.crossing_exterior, dotProduct_smul, dotProduct_add, dotProduct_smul,
      ← dotProduct_transpose_mulVec, hOdd, dotProduct_sub, dotProduct_smul,
      dotProduct_comm (B.oddSource j) (B.oddPotential i),
      dotProduct_comm (B.oddSource j) (B.oddSource i)]
    simp only [smul_eq_mul]
    ring
  refine ⟨hKer, fun i j ↦ ?_⟩
  have hSplit (k : ι) : B.residual k + B.projected k = B.exterior k := by
    rw [residual, sub_add_cancel]
  have hGram : B.exterior i ⬝ᵥ B.exterior j =
      B.residual i ⬝ᵥ B.residual j + B.projected i ⬝ᵥ B.projected j := by
    rw [← hSplit i, ← hSplit j, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm (B.projected i) (B.residual j),
      B.dot_projected_eq_zero i _ (hKer j), zero_add,
      B.dot_projected_eq_zero j _ (hKer i), add_zero]
  change (B.size / 6) * (9 * (if i = j then (1 : ℝ) else 0) - 1) -
    (B.evenPotential i ⬝ᵥ B.evenSource j + B.oddPotential i ⬝ᵥ B.oddSource j) = _
  linear_combination 3 * hGram + 3 * hProjected i j - 3 * B.exterior_gram i j

/-- For two separated blocks on the same exterior parity, the off-diagonal entries are the
original exterior pairings scaled by three. The full matrix is positive semidefinite and its
rank is bounded by the dimension of the common crossing kernel. -/
theorem joint_green_defect
    {e' o' κ : Type*} [Fintype e'] [DecidableEq e'] [Fintype o'] [DecidableEq κ]
    [Fintype ι] [Fintype κ]
    (C : GreenBlock e o n ι) (D : GreenBlock e' o' n κ)
    (hCross : C.crossing * D.crossingᵀ = 0)
    (hC : ∀ j, C.crossing *ᵥ D.exterior j = 0)
    (hD : ∀ i, D.crossing *ᵥ C.exterior i = 0) :
    let K := LinearMap.ker C.crossing.mulVecLin ⊓ LinearMap.ker D.crossing.mulVecLin
    let r := Sum.elim C.residual D.residual
    let R : Matrix n (ι ⊕ κ) ℝ := of fun a i ↦ r i a
    let B : Matrix ι κ ℝ := of fun i j ↦ 3 * (C.exterior i ⬝ᵥ D.exterior j)
    let G := fromBlocks C.defect B Bᵀ D.defect
    (∀ i, r i ∈ K) ∧
    (∀ i j, C.residual i ⬝ᵥ D.residual j = C.exterior i ⬝ᵥ D.exterior j) ∧
    G = (3 : ℝ) • (Rᵀ * R) ∧ G.PosSemidef ∧ G.rank ≤ Module.finrank ℝ K := by
  intro K r R B G
  obtain ⟨hCKer, hCDefect⟩ := C.green_defect
  obtain ⟨hDKer, hDDefect⟩ := D.green_defect
  have hCross' : D.crossing * C.crossingᵀ = 0 := by
    simpa using congrArg Matrix.transpose hCross
  have hCD (j : κ) : C.crossing *ᵥ D.residual j = 0 := by
    rw [residual, mulVec_sub, hC, projected, mulVec_smul, mulVec_mulVec, hCross,
      zero_mulVec, smul_zero, sub_zero]
  have hDC (i : ι) : D.crossing *ᵥ C.residual i = 0 := by
    rw [residual, mulVec_sub, hD, projected, mulVec_smul, mulVec_mulVec, hCross',
      zero_mulVec, smul_zero, sub_zero]
  have hKer (i : ι ⊕ κ) : r i ∈ K := by
    cases i with
    | inl i => exact ⟨hCKer i, hDC i⟩
    | inr j => exact ⟨hCD j, hDKer j⟩
  have hPair (i : ι) (j : κ) :
      C.residual i ⬝ᵥ D.residual j = C.exterior i ⬝ᵥ D.exterior j := by
    calc
      C.residual i ⬝ᵥ D.residual j = C.residual i ⬝ᵥ D.exterior j := by
        change C.residual i ⬝ᵥ (D.exterior j - D.projected j) = _
        rw [dotProduct_sub, D.dot_projected_eq_zero j _ (hDC i), sub_zero]
      _ = C.exterior i ⬝ᵥ D.exterior j := by
        change (C.exterior i - C.projected i) ⬝ᵥ D.exterior j = _
        rw [sub_dotProduct, dotProduct_comm (C.projected i),
          C.dot_projected_eq_zero i _ (hC j), sub_zero]
  have hGram : G = (3 : ℝ) • (Rᵀ * R) := by
    ext i j
    change G i j = 3 * (r i ⬝ᵥ r j)
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hCDefect i j
      | inr j =>
        change 3 * (C.exterior i ⬝ᵥ D.exterior j) = 3 * (C.residual i ⬝ᵥ D.residual j)
        rw [hPair]
    | inr i =>
      cases j with
      | inl j =>
        change 3 * (C.exterior j ⬝ᵥ D.exterior i) = 3 * (D.residual i ⬝ᵥ C.residual j)
        rw [dotProduct_comm (D.residual i), hPair]
      | inr j => exact hDDefect i j
  refine ⟨hKer, hPair, hGram, ?_, ?_⟩
  · rw [hGram, ← conjTranspose_eq_transpose_of_trivial]
    exact (posSemidef_conjTranspose_mul_self R).smul (by positivity)
  · rw [hGram, ← Matrix.smul_mul]
    refine (rank_mul_le_right _ R).trans ?_
    rw [rank_eq_finrank_span_cols]
    exact Submodule.finrank_mono
      (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hKer i))

end GreenBlock

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenDefect
