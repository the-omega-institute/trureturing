/- GID: D5/S3/Quantum/Recovery/PetzDiagonalBKMOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PetzDiagonalBKMOptimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The sharp full-fibre quotient with the actual Umegaki BKM Hessian at a diagonal base. -/

import D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum
import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich

/-! Evaluation of the actual diagonal Hessian in the fixed retained and flag coordinates. -/

noncomputable section

set_option autoImplicit false

namespace D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder
open D5.S3.Divergence.LogDerivTrace (logDeriv logDeriv_integrable)
open D5.S3.Divergence.MeanKernels.LogarithmicMeanSandwich (logMean_kernel_sandwich)
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM (pair_kernel_eval)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Recovery.PetzProjectedHessian
open D5.S3.Quantum.Recovery.PetzWeightedHessianOptimum

/-- The reciprocal of the scalar resolvent kernel, including coincident eigenvalues. -/
def diagonalWeights (β : Slot → ℝ) : Weights := fun i j =>
  (if β i = β j then 1 / β i else (Real.log (β i) - Real.log (β j)) / (β i - β j))⁻¹

private theorem weights_pos_le (β : Slot → ℝ) (hβ : ∀ i, 0 < β i) (i j : Slot) :
    0 < diagonalWeights β i j ∧ diagonalWeights β i j ≤ (β i + β j) / 2 := by
  by_cases h : β i = β j
  · simp only [diagonalWeights, ite_eq_left h, one_div, inv_inv, ← h]
    exact ⟨hβ i, by linarith⟩
  · rw [diagonalWeights, ite_eq_right h]
    have hlow : 0 < 2 / (β i + β j) := div_pos (by norm_num) (add_pos (hβ i) (hβ j))
    have hs := (logMean_kernel_sandwich (hβ i) (hβ j) h).1
    refine ⟨inv_pos.mpr (lt_of_lt_of_le hlow hs), ?_⟩
    have hi := inv_anti₀ hlow hs
    simpa [div_eq_mul_inv, mul_comm] using hi

private theorem weights_symm (β : Slot → ℝ) (i j : Slot) :
    diagonalWeights β i j = diagonalWeights β j i := by
  by_cases h : β i = β j
  · simp [diagonalWeights, h]
  · simp only [diagonalWeights, ite_eq_right h, ite_eq_right h.symm]
    rw [show Real.log (β j) - Real.log (β i) = -(Real.log (β i) - Real.log (β j)) by ring,
      show β j - β i = -(β i - β j) by ring, neg_div_neg_eq]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private theorem logDeriv_entry (β : Slot → ℝ) (hβ : ∀ i, 0 < β i) (Z : Joint) (i j : Slot) :
    logDeriv (Matrix.diagonal fun k => (β k : ℂ)) Z i j =
      ((diagonalWeights β i j)⁻¹ : ℝ) * Z i j := by
  let ρ : Joint := Matrix.diagonal fun k => (β k : ℂ)
  have hρ : ρ.PosDef := Matrix.PosDef.diagonal fun k => by exact_mod_cast hβ k
  let L : Joint →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i)
  have hinter := L.integral_comp_comm (logDeriv_integrable ρ Z hρ)
  change (∫ t in Set.Ioi (0 : ℝ), ((ρ + t • 1)⁻¹ * Z * (ρ + t • 1)⁻¹) i j) =
    logDeriv ρ Z i j at hinter
  rw [← hinter]
  have hres (t : ℝ) : (ρ + t • 1)⁻¹ =
      Matrix.diagonal fun k => (((β k + t : ℝ) : ℂ)⁻¹) := by
    have hd : ρ + t • 1 = Matrix.diagonal fun k => ((β k + t : ℝ) : ℂ) := by
      ext k l
      by_cases h : k = l <;> simp [ρ, Matrix.diagonal_apply, Matrix.one_apply, h]
    rw [hd, Matrix.inv_diagonal]
    rfl
  simp only [hres, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have heq (t : ℝ) :
      ((β i + t : ℝ) : ℂ)⁻¹ * Z i j * ((β j + t : ℝ) : ℂ)⁻¹ =
        ((1 / ((β i + t) * (β j + t)) : ℝ) : ℂ) * Z i j := by
    push_cast
    rw [one_div, mul_inv_rev]
    ac_rfl
  simp_rw [heq]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_complex_ofReal,
    pair_kernel_eval _ _ (hβ i) (hβ j)]
  simp only [diagonalWeights, inv_inv]

private theorem diagonal_energy (β : Slot → ℝ) (hβ : ∀ i, 0 < β i) (Z : Joint)
    (hZ : Z.IsHermitian) :
    (Z * logDeriv (Matrix.diagonal fun i => (β i : ℂ)) Z).trace.re =
      energy (diagonalWeights β) Z := by
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum, energy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [logDeriv_entry β hβ, mul_assoc, ← hZ.apply j i, Complex.star_def,
    Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, div_eq_mul_inv, mul_comm]

/-- The exact quotient and its unique tangent optimizer for the actual
diagonal Umegaki Hessian on the full partial-trace-zero fibre. -/
theorem diagonal_bkm_maximum (β : Slot → ℝ) (C f g : ℝ)
    (hβ : ∀ i, 0 < β i) (hC : 0 < C) (hf : 0 < f) (hg : 0 < g)
    (h₀ : 0 ≤ margin β (reducedWeight (diagonalWeights β) 0 1) C f g 0)
    (h₁ : 0 ≤ margin β (reducedWeight (diagonalWeights β) 0 1) C f g 1)
    (hstrict : 0 < margin β (reducedWeight (diagonalWeights β) 0 1) C f g 0 +
      margin β (reducedWeight (diagonalWeights β) 0 1) C f g 1) :
    let m := reducedWeight (diagonalWeights β) 0 1
    let ρ := Matrix.diagonal fun i => (β i : ℂ)
    let ratio (Z : Joint) := traceNorm (Z + offset f g) ^ 2 /
      (C + (Z * logDeriv ρ Z).trace.re / 2)
    let opt := 16 * m + (f + g) ^ 2 / C
    IsGreatest (ratio '' fibre) opt ∧
      ∀ Z ∈ fibre, ratio Z = opt ↔ Z = optimizer m C f g := by
  dsimp only
  let w := diagonalWeights β
  have hw (i j : Slot) := weights_pos_le β hβ i j
  have h := weighted_hessian_maximum w β C f g (fun i j => (hw i j).1) (weights_symm β)
    (fun i => (hβ i).le) (fun i j _ => (hw i j).2) hC hf hg h₀ h₁ hstrict
  let ratio (Z : Joint) := traceNorm (Z + offset f g) ^ 2 /
    (C + (Z * logDeriv (Matrix.diagonal fun i => (β i : ℂ)) Z).trace.re / 2)
  let weighted (Z : Joint) := traceNorm (Z + offset f g) ^ 2 / (C + energy w Z / 2)
  have he (Z : Joint) (hZ : Z ∈ fibre) : ratio Z = weighted Z := by
    dsimp [ratio, weighted, w]
    rw [diagonal_energy β hβ Z hZ.1]
  change IsGreatest (ratio '' fibre) _ ∧ ∀ Z ∈ fibre, ratio Z = _ ↔ _
  rw [show ratio '' fibre = weighted '' fibre from Set.image_congr (fun Z hZ => he Z hZ)]
  exact ⟨h.1, fun Z hZ => by rw [he Z hZ]; exact h.2 Z hZ⟩

#print axioms diagonal_bkm_maximum

end D5.S3.Quantum.Recovery.PetzDiagonalBKMOptimum
