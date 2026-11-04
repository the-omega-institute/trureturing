/- GID: D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim; result=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result; claim=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim
   digest: The Fuchs--Caves fidelity measurement has a nonoptimal ROC point in dimension three. -/

import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation

open _root_.Matrix
open D5.S3.Quantum.Recovery.ProductPrefixRigidity (readout)
open scoped BigOperators ComplexOrder MatrixOrder

/-- The optimal ROC boundary at a fixed false-positive coordinate. -/
def onOptimalROC {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (x y : ℝ) : Prop :=
  ∀ f, f ∈ Set.Icc 0 1 → (f * ρ).trace.re = x → (f * σ).trace.re ≤ y

/-- The Fuchs--Caves fidelity observable. -/
def fidelityObservable {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (CFC.sqrt ρ)⁻¹ * CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ) * (CFC.sqrt ρ)⁻¹

/-- The cumulative probability of the first measurement outcomes. -/
noncomputable def cumulative {d : ℕ} (a : Fin d → Fin d → ℂ)
    (m : Matrix (Fin d) (Fin d) ℂ) (k : Fin (d + 1)) : ℝ :=
  Finset.sum (Finset.univ.filter (fun i : Fin d => i.val < k.val)) (fun i => readout m (a i))

def isOrderedFidelityEigenbasis {d : ℕ}
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) (a : Fin d → Fin d → ℂ) : Prop :=
  (∀ i, ∑ j, star (a i j) * a i j = 1) ∧
  (∀ i j, i ≠ j → ∑ k, star (a i k) * a j k = 0) ∧
  (∀ i, ∃ r : ℝ, fidelityObservable ρ σ *ᵥ a i = (r : ℂ) • a i) ∧
  (∀ i j, i ≤ j → readout σ (a i) * readout ρ (a j) ≥ readout σ (a j) * readout ρ (a i))

/-- Bodor--Koniorczyk's question for the Fuchs--Caves measurement. -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ σ : Matrix (Fin d) (Fin d) ℂ),
    ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 →
    ∀ a : Fin d → Fin d → ℂ,
      isOrderedFidelityEigenbasis ρ σ a →
      ∀ k : Fin (d + 1),
        onOptimalROC ρ σ (cumulative a ρ k)
          (cumulative a σ k)

private noncomputable def rho : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 20 : ℝ) • !![2, 1, 1; 1, 10, 1; 1, 1, 8]

private noncomputable def sigma : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 40 : ℝ) • !![16, 4, 2; 4, 20, 1; 2, 1, 4]

private noncomputable def diagonal : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i : Fin 3 =>
    if i = 0 then (2 : ℂ) else if i = 1 then 1 else (1 / 2 : ℂ))

private noncomputable def competitor : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 1382 : ℝ) • !![1369, 74, -111; 74, 4, -6; -111, -6, 9]

private theorem diagonal_posDef : diagonal.PosDef := by
  rw [diagonal]
  exact Matrix.PosDef.diagonal (d := fun i : Fin 3 =>
    (if i = 0 then (2 : ℂ) else if i = 1 then 1 else (1 / 2 : ℂ))) (by
      intro i
      fin_cases i <;> norm_num)

private theorem rho_posDef : rho.PosDef := by
  let j : Matrix (Fin 3) (Fin 3) ℂ :=
    Matrix.vecMulVec (fun _ : Fin 3 => (1 : ℂ)) (star (fun _ : Fin 3 => (1 : ℂ)))
  let hdiag : (Matrix.diagonal (fun i : Fin 3 =>
      (if i = 0 then (1 : ℂ) else if i = 1 then 9 else 7))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  have hj : j.PosSemidef := by
    exact Matrix.posSemidef_vecMulVec_self_star _
  have hbase : (j + Matrix.diagonal (fun i : Fin 3 =>
      (if i = 0 then (1 : ℂ) else if i = 1 then 9 else 7))).PosDef :=
    by simpa [add_comm] using hdiag.add_posSemidef hj
  have hscaled := hbase.smul (show (0 : ℝ) < 1 / 20 by norm_num)
  have hmatrix :
      (!![2, 1, 1; 1, 10, 1; 1, 1, 8] : Matrix (Fin 3) (Fin 3) ℂ) =
        j + Matrix.diagonal (fun i : Fin 3 =>
          (if i = 0 then (1 : ℂ) else if i = 1 then 9 else 7)) := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      norm_num [j, Matrix.vecMulVec, Matrix.diagonal, Matrix.of_apply]
  rw [rho, hmatrix]
  exact hscaled

private theorem rho_trace : rho.trace = 1 := by
  norm_num [rho, Matrix.trace, Matrix.smul_apply, Fin.sum_univ_succ]

-- The explicit 3x3 congruence identity needs a larger elaboration budget.
set_option maxHeartbeats 2000000 in
private theorem sigma_eq : sigma = diagonal * rho * diagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sigma, diagonal, rho, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

private theorem sigma_posDef : sigma.PosDef := by
  rw [sigma_eq]
  have hcong := rho_posDef.mul_mul_conjTranspose_same (B := diagonal)
    (Matrix.vecMul_injective_of_isUnit diagonal_posDef.isUnit)
  have hstar : diagonalᴴ = diagonal := diagonal_posDef.isHermitian.eq
  simpa only [hstar] using hcong

private theorem sigma_trace : sigma.trace = 1 := by
  rw [sigma]
  norm_num [Matrix.trace, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem sqrt_observable : fidelityObservable rho sigma = diagonal := by
  rw [fidelityObservable]
  have hs : (CFC.sqrt rho).PosDef := rho_posDef.isStrictlyPositive.sqrt.posDef
  have hm : (CFC.sqrt rho * sigma * CFC.sqrt rho).PosDef := by
    simpa only [star_eq_conjTranspose, hs.isHermitian.eq] using
      hs.isUnit.posDef_star_right_conjugate_iff.mpr sigma_posDef
  have hhalf := D5.S3.Quantum.Matrix.AlternativeMeanLinearization.half_eq_sqrt rho_posDef
  have hinv : (CFC.sqrt rho)⁻¹ = cfc (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) rho :=
    Matrix.inv_eq_right_inv (by
      simpa only [hhalf] using
        (D5.S3.Quantum.Matrix.AlternativeMeanLinearization.half_inverse rho_posDef).1)
  have h := D5.S3.Quantum.Matrix.AlternativeMeanLinearization.riccati_unique
    rho_posDef diagonal_posDef sigma_eq.symm
  simp only [D5.S3.Quantum.Matrix.AlternativeMeanLinearization.gmInv, hhalf,
    D5.S3.Quantum.Matrix.AlternativeMeanLinearization.half_eq_sqrt hm] at h
  simpa only [hinv] using h

private theorem coordinate_basis_ordered :
    isOrderedFidelityEigenbasis rho sigma (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  unfold isOrderedFidelityEigenbasis
  rw [sqrt_observable]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      apply Complex.ext <;>
        norm_num [Matrix.one_apply, star, dotProduct, Fin.sum_univ_succ, RCLike.star_def,
          map_ofNat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.one_apply, star, dotProduct, Fin.sum_univ_succ, RCLike.star_def,
        map_ofNat, Complex.ext_iff]
  · intro i
    fin_cases i
    · refine ⟨2, ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, Matrix.mulVec_diagonal, Matrix.one_apply]
    · refine ⟨1, ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, Matrix.mulVec_diagonal, Matrix.one_apply]
    · refine ⟨(1 / 2 : ℝ), ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, Matrix.mulVec_diagonal, Matrix.one_apply]
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      try norm_num at hij
    all_goals
      norm_num [readout, Matrix.one_apply, rho, sigma, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

private noncomputable def competitorVector : Fin 3 → ℂ := ![37, 2, -3]

private theorem competitor_eq :
    competitor = (1 / 1382 : ℝ) •
      Matrix.vecMulVec competitorVector (star competitorVector) := by
  rw [competitor, competitorVector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.vecMulVec, Matrix.smul_apply,
      Pi.star_apply, RCLike.star_def, map_ofNat]

private theorem competitor_binary : competitor ∈ Set.Icc 0 1 := by
  change 0 ≤ competitor ∧ competitor ≤ 1
  constructor
  · rw [competitor_eq]
    exact ((Matrix.posSemidef_vecMulVec_self_star competitorVector).smul
      (by norm_num)).nonneg
  · apply Matrix.le_iff.mpr
    have hv : ∑ j, ‖competitorVector j‖ ^ 2 = (1382 : ℝ) := by
      norm_num [competitorVector, Fin.sum_univ_succ]
    have h := D5.S3.Quantum.Entanglement.AbsoluteSeparability.LowRankRays.rank_one_upper competitorVector
    have h' : (((1382 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
        Matrix.vecMulVec competitorVector (star competitorVector)).PosSemidef := by
      simpa [hv] using h
    have hs := h'.smul (show (0 : ℝ) ≤ 1 / 1382 by norm_num)
    have heq : 1 - competitor = (1 / 1382 : ℝ) •
        (((1382 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
          Matrix.vecMulVec competitorVector (star competitorVector)) := by
      rw [competitor_eq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [competitorVector, Matrix.vecMulVec, Matrix.smul_apply, hv,
          Matrix.one_apply, Pi.star_apply, RCLike.star_def, map_ofNat]
    rw [heq]
    exact hs

private theorem competitor_rho_trace : (competitor * rho).trace.re = 1 / 10 := by
  norm_num [competitor, rho, Matrix.trace, Matrix.mul_apply, Matrix.smul_apply,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

private theorem competitor_sigma_trace : (competitor * sigma).trace.re = 5539 / 13820 := by
  norm_num [competitor, sigma, Matrix.trace, Matrix.mul_apply, Matrix.smul_apply,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

private theorem cumulative_first_rho :
    cumulative (1 : Matrix (Fin 3) (Fin 3) ℂ) rho ⟨1, by decide⟩ = 1 / 10 := by
  change Finset.sum (Finset.univ.filter (fun i : Fin 3 => i.val < 1))
      (fun i => readout rho ((1 : Matrix (Fin 3) (Fin 3) ℂ) i)) = 1 / 10
  rw [show Finset.univ.filter (fun i : Fin 3 => i.val < 1) = {0} by decide]
  rw [Finset.sum_singleton, readout]
  norm_num [Matrix.one_apply, rho, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

private theorem cumulative_first_sigma :
    cumulative (1 : Matrix (Fin 3) (Fin 3) ℂ) sigma ⟨1, by decide⟩ = 2 / 5 := by
  change Finset.sum (Finset.univ.filter (fun i : Fin 3 => i.val < 1))
      (fun i => readout sigma ((1 : Matrix (Fin 3) (Fin 3) ℂ) i)) = 2 / 5
  rw [show Finset.univ.filter (fun i : Fin 3 => i.val < 1) = {0} by decide]
  norm_num [readout, Matrix.one_apply, sigma, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

/-- The preregistered three-dimensional witness refutes the open question. -/
theorem result : ¬ claim := by
  intro h
  have hroc := h 3 rho sigma rho_posDef rho_trace sigma_posDef sigma_trace
    (1 : Matrix (Fin 3) (Fin 3) ℂ) coordinate_basis_ordered ⟨1, by decide⟩
  have hle := hroc competitor competitor_binary (by
    rw [competitor_rho_trace, cumulative_first_rho])
  rw [competitor_sigma_trace, cumulative_first_sigma] at hle
  norm_num at hle

end D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation
