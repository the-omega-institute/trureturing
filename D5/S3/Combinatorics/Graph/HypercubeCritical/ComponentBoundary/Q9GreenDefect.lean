/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9GreenDefect
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Mul]
   utility: none
   digest: The Q9 Green defect is the Gram form of the crossing-kernel residuals. -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The finite linear algebra underlying the Green identity for a Q9 block. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9GreenDefect

open Matrix

/-- Supplied Laplacian solutions determine the row-space part of the crossing data.
The Green defect is the Gram form of the remaining vectors, with coefficient `3 / 2`.
An injective crossing map forces this defect to vanish. -/
theorem green_defect {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq ι]
    (L : Matrix m m ℝ) (X : Matrix m n ℝ) (N : ℝ)
    (h b : ι → m → ℝ) (z : ι → n → ℝ)
    (hL : L.IsSymm)
    (hXX : X * Xᵀ = L * ((6 : ℝ) • 1 - L))
    (hh : ∀ i, L *ᵥ h i = b i)
    (hz : ∀ i, X *ᵥ z i = (-1 / 3 : ℝ) • (((6 : ℝ) • 1 - L) *ᵥ b i))
    (hGram : ∀ i j, z i ⬝ᵥ z j + (b i ⬝ᵥ b j) / 9 =
      N * ((if i = j then (1 : ℝ) else 0) - 1 / 9)) :
    let y (i : ι) := (-1 / 3 : ℝ) • (Xᵀ *ᵥ h i)
    let r (i : ι) := z i - y i
    (∀ i, X *ᵥ r i = 0) ∧
    (∀ i j, y i ⬝ᵥ r j = 0) ∧
    (∀ i j, (N / 6) * (9 * (if i = j then (1 : ℝ) else 0) - 1) - h i ⬝ᵥ b j =
      (3 / 2 : ℝ) * (r i ⬝ᵥ r j)) ∧
    (Function.Injective X.mulVec → ∀ i j,
      h i ⬝ᵥ b j = (N / 6) * (9 * (if i = j then (1 : ℝ) else 0) - 1)) := by
  intro y r
  have hcomm : L * ((6 : ℝ) • 1 - L) = ((6 : ℝ) • 1 - L) * L := by
    simp [mul_sub, sub_mul]
  have hXy (i : ι) : X *ᵥ y i = (-1 / 3 : ℝ) • (((6 : ℝ) • 1 - L) *ᵥ b i) := by
    dsimp only [y]
    rw [mulVec_smul, mulVec_mulVec, hXX, hcomm, ← mulVec_mulVec, hh]
  have hXr (i : ι) : X *ᵥ r i = 0 := by
    change X *ᵥ (z i - y i) = 0
    rw [mulVec_sub, hz, hXy, sub_self]
  have horth (i j : ι) : y i ⬝ᵥ r j = 0 := by
    change ((-1 / 3 : ℝ) • (Xᵀ *ᵥ h i)) ⬝ᵥ r j = 0
    rw [smul_dotProduct, dotProduct_comm (Xᵀ *ᵥ h i), dotProduct_transpose_mulVec, hXr]
    simp
  have hyy (i j : ι) : y i ⬝ᵥ y j = (6 * (h i ⬝ᵥ b j) - b i ⬝ᵥ b j) / 9 := by
    change ((-1 / 3 : ℝ) • (Xᵀ *ᵥ h i)) ⬝ᵥ y j = _
    rw [smul_dotProduct, dotProduct_comm (Xᵀ *ᵥ h i), dotProduct_transpose_mulVec,
      hXy, dotProduct_smul, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, hL.dotProduct_mulVec_comm (x := h i), hh, dotProduct_comm (b j) (b i)]
    simp only [smul_eq_mul]
    ring
  have hsplit (i : ι) : y i + r i = z i := by
    change y i + (z i - y i) = z i
    exact add_sub_cancel _ _
  have hsum (i j : ι) : z i ⬝ᵥ z j = y i ⬝ᵥ y j + r i ⬝ᵥ r j := by
    calc
      z i ⬝ᵥ z j = (y i + r i) ⬝ᵥ (y j + r j) := by rw [hsplit, hsplit]
      _ = y i ⬝ᵥ y j + r i ⬝ᵥ r j := by
        rw [add_dotProduct, dotProduct_add, dotProduct_add, horth,
          dotProduct_comm (r i) (y j), horth, add_zero, zero_add]
  have hdefect (i j : ι) :
      (N / 6) * (9 * (if i = j then (1 : ℝ) else 0) - 1) - h i ⬝ᵥ b j =
        (3 / 2 : ℝ) * (r i ⬝ᵥ r j) := by
    linear_combination (3 / 2 : ℝ) * (hsum i j) + (3 / 2 : ℝ) * (hyy i j) -
      (3 / 2 : ℝ) * (hGram i j)
  refine ⟨hXr, horth, hdefect, ?_⟩
  intro hX i j
  have hr : r i = 0 := hX (by rw [hXr, mulVec_zero])
  have hij := hdefect i j
  rw [hr, zero_dotProduct, mul_zero] at hij
  exact (sub_eq_zero.mp hij).symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9GreenDefect
