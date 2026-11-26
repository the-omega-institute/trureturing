/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/TriangleSurplusAllocation
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cleared adjugate surpluses give a weighted triangle Gram allocation. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleGram
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleSurplusFormula

/-! Scalar inequalities for the exact Cramer solution of the triangle system. -/

namespace RefinedBMV.Tracial.TriangleSurplus

open Matrix ThreeBlockGram
open private ThreeBlockGram.triangleScale from
  D5.S3.Quantum.Analysis.RefinedBMV.Tracial.TriangleGram

noncomputable section

private theorem clearedOfEntries_eq (a b c d e f l₀ l₁ l₂ : ℝ)
    (e₀₁ e₀₂ e₁₂ : Edge ℝ) (w₀₁ w₀₂ w₁₂ : ℝ) :
    let T : Matrix (Fin 3) (Fin 3) ℝ := !![a, b, c; b, d, e; c, e, f]
    let U := T.adjugate *ᵥ ![l₀, l₁, l₂]
    clearedOfEntries a b c d e f l₀ l₁ l₂ e₀₁ e₀₂ e₁₂ w₀₁ w₀₂ w₁₂ =
      (T.det ^ 2 - 2 * w₀₁ ^ 2 * e₀₁.form (U 0) (U 1),
       T.det ^ 2 - 2 * w₀₂ ^ 2 * e₀₂.form (U 0) (U 2),
       T.det ^ 2 - 2 * w₁₂ ^ 2 * e₁₂.form (U 1) (U 2)) := by
  dsimp only
  have hd : (!![a, b, c; b, d, e; c, e, f] : Matrix (Fin 3) (Fin 3) ℝ).det =
      a * (d * f - e ^ 2) + b * (c * e - b * f) + c * (b * e - c * d) := by
    rw [Matrix.det_fin_three]
    simp
    ring
  rw [hd, Matrix.adjugate_fin_three_of]
  simp [clearedOfEntries, mulVec, dotProduct, Fin.sum_univ_three, pow_two,
    sub_eq_add_neg, add_comm, mul_comm b c, mul_comm c e, mul_comm c d]

def kernelEdge (K : Kernel) (i j k : Fin 3) : Edge ℝ :=
  edge (h K k i j) (f K i j) (g K i j) (f K j i)

def kernelSurplus (K : Kernel) (w : Fin 3 → ℝ) : ℝ × ℝ × ℝ :=
  cleared (triangleDemand K 0) (triangleDemand K 1) (triangleDemand K 2)
    (kernelEdge K 0 1 2) (kernelEdge K 0 2 1) (kernelEdge K 1 2 0) (w 2) (w 1) (w 0)

private theorem kernelSurplus_eq (K : Kernel) (w : Fin 3 → ℝ) :
    let T := (2 : ℝ) • triangleMatrix K w
    let U := T.adjugate *ᵥ triangleDemand K
    kernelSurplus K w =
      (T.det ^ 2 - 2 * (w 2) ^ 2 * (kernelEdge K 0 1 2).form (U 0) (U 1),
       T.det ^ 2 - 2 * (w 1) ^ 2 * (kernelEdge K 0 2 1).form (U 0) (U 2),
       T.det ^ 2 - 2 * (w 0) ^ 2 * (kernelEdge K 1 2 0).form (U 1) (U 2)) := by
  dsimp only
  simp only [kernelSurplus, cleared]
  rw [clearedOfEntries_eq]
  have hT : (2 : ℝ) • triangleMatrix K w =
      !![w 2 * (kernelEdge K 0 1 2).left + w 1 * (kernelEdge K 0 2 1).left,
         w 2 * (kernelEdge K 0 1 2).cross, w 1 * (kernelEdge K 0 2 1).cross;
         w 2 * (kernelEdge K 0 1 2).cross,
         w 2 * (kernelEdge K 0 1 2).right + w 0 * (kernelEdge K 1 2 0).left,
         w 0 * (kernelEdge K 1 2 0).cross;
         w 1 * (kernelEdge K 0 2 1).cross, w 0 * (kernelEdge K 1 2 0).cross,
         w 1 * (kernelEdge K 0 2 1).right + w 0 * (kernelEdge K 1 2 0).right] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, triangleMatrix, ThreeBlockGram.triangleScale, triangleDemand,
        kernelEdge, edge, smul_eq_mul] <;> ring
  rw [hT]
  rfl

private theorem edge_energy_of_cleared (K : Kernel) (w : Fin 3 → ℝ) {i j k : Fin 3}
    (hd : triangleDemand K k = h K k i j) (hh : 0 ≤ h K k i j)
    (hn : (triangleMatrix K w).det ≠ 0)
    (hc : let T := (2 : ℝ) • triangleMatrix K w
          let U := T.adjugate *ᵥ triangleDemand K
          0 ≤ T.det ^ 2 - 2 * (w k) ^ 2 * (kernelEdge K i j k).form (U i) (U j)) :
    triangleEdgeEnergy K w (triangleSolution K w) i j k ≤ h K k i j := by
  let M := triangleMatrix K w
  let l := triangleDemand K
  let D := M.det
  let V := M.adjugate *ᵥ l
  let E := kernelEdge K i j k
  have he : triangleEdgeEnergy K w (triangleSolution K w) i j k * D ^ 2 =
      h K k i j * ((w k) ^ 2 * E.form (V i) (V j) / 2) := by
    simp only [triangleEdgeEnergy, ThreeBlockGram.triangleScale, hd, triangleSolution, Pi.smul_apply, smul_eq_mul,
      E, kernelEdge, edge, Edge.form, Nat.cast_ofNat, D, M, V, l]
    field_simp [hn]
  change 0 ≤ ((2 : ℝ) • M).det ^ 2 - 2 * (w k) ^ 2 *
    E.form ((((2 : ℝ) • M).adjugate *ᵥ l) i) ((((2 : ℝ) • M).adjugate *ᵥ l) j) at hc
  simp only [Matrix.det_smul, Matrix.adjugate_smul, Fintype.card_fin, Matrix.smul_mulVec,
    Pi.smul_apply, smul_eq_mul] at hc
  have hc' : 0 ≤ D ^ 2 - (w k) ^ 2 * E.form (V i) (V j) / 2 := by
    have hscale : ((2 : ℝ) ^ (3 : ℕ) * D) ^ 2 -
        2 * (w k) ^ 2 * E.form ((2 : ℝ) ^ (3 - 1 : ℕ) * V i) ((2 : ℝ) ^ (3 - 1 : ℕ) * V j) =
        64 * (D ^ 2 - (w k) ^ 2 * E.form (V i) (V j) / 2) := by
      simp only [Edge.form, Nat.cast_ofNat]
      ring
    rw [hscale] at hc
    exact nonneg_of_mul_nonneg_right hc (by norm_num)
  apply (le_of_mul_le_mul_right ?_ (sq_pos_of_ne_zero (show D ≠ 0 from hn)))
  rw [he]
  exact mul_le_mul_of_nonneg_left (sub_nonneg.mp hc') hh

/-- Nonnegative cleared surpluses pay the three edge energies of the weighted
triangle allocation when the triangle system is invertible. -/
theorem allocation_of_kernelSurplus (K : Kernel) (w : Fin 3 → ℝ)
    (hn : (triangleMatrix K w).det ≠ 0)
    (hg : ∀ i j, g K i j = g K j i)
    (hf : ∀ i j, i ≠ j → 0 < f K i j)
    (hdet : ∀ i j, i ≠ j → (g K i j / 2) ^ 2 ≤ f K i j * f K j i)
    (hh₀₁ : 0 ≤ h K 2 0 1) (hh₀₂ : 0 ≤ h K 1 0 2) (hh₁₂ : 0 ≤ h K 0 1 2)
    (hc₀₁ : 0 ≤ (kernelSurplus K w).1)
    (hc₀₂ : 0 ≤ (kernelSurplus K w).2.1)
    (hc₁₂ : 0 ≤ (kernelSurplus K w).2.2) :
    Allocation K (weightedTriangleAllocation K w (triangleSolution K w)) := by
  rw [kernelSurplus_eq] at hc₀₁ hc₀₂ hc₁₂
  exact allocation_of_triangleMatrix_mulVec K w _ (triangleMatrix_mulVec_solution K w hn)
    hg hf hdet (edge_energy_of_cleared K w rfl hh₀₁ hn hc₀₁)
    (edge_energy_of_cleared K w rfl hh₀₂ hn hc₀₂)
    (edge_energy_of_cleared K w rfl hh₁₂ hn hc₁₂)

#print axioms allocation_of_kernelSurplus

end

end RefinedBMV.Tracial.TriangleSurplus
