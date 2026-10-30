/- GID: D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim; result=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result; claim=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim
   digest: The Fuchs--Caves fidelity measurement has a nonoptimal ROC point in dimension three. -/

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- A binary quantum test is an effect between zero and the identity. -/
def isBinaryTest {d : ℕ} (f : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  0 ≤ f ∧ f ≤ 1

/-- The optimal ROC boundary at a fixed false-positive coordinate. -/
def onOptimalROC {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ)
    (x y : ℝ) : Prop :=
  ∀ f, isBinaryTest f → (f * ρ).trace.re = x → (f * σ).trace.re ≤ y

/-- The Fuchs--Caves fidelity observable. -/
def fidelityObservable {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (CFC.sqrt ρ)⁻¹ * CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ) * (CFC.sqrt ρ)⁻¹

noncomputable def outcome {d : ℕ} (a : Fin d → Fin d → ℂ)
    (m : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : ℝ :=
  ((star (a i)) ⬝ᵥ (m *ᵥ a i)).re

private noncomputable def cumulative {d : ℕ} (a : Fin d → Fin d → ℂ)
    (m : Matrix (Fin d) (Fin d) ℂ) (k : Fin (d + 1)) : ℝ :=
  Finset.sum (Finset.univ.filter (fun i : Fin d => i.val < k.val)) (outcome a m)

def isOrderedFidelityEigenbasis {d : ℕ}
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) (a : Fin d → Fin d → ℂ) : Prop :=
  (∀ i, ∑ j, star (a i j) * a i j = 1) ∧
  (∀ i j, i ≠ j → ∑ k, star (a i k) * a j k = 0) ∧
  (∀ i, ∃ r : ℝ, fidelityObservable ρ σ *ᵥ a i = (r : ℂ) • a i) ∧
  (∀ i j, i ≤ j → outcome a σ i * outcome a ρ j ≥ outcome a σ j * outcome a ρ i)

/-- The cumulative false-positive coordinate of an ordered eigenbasis measurement. -/
def cumulativeFalsePositive {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d → Fin d → ℂ) (k : Fin (d + 1)) : ℝ :=
  cumulative a ρ k

/-- The cumulative true-positive coordinate of an ordered eigenbasis measurement. -/
def cumulativeTruePositive {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ)
    (a : Fin d → Fin d → ℂ) (k : Fin (d + 1)) : ℝ :=
  cumulative a σ k

/-- Bodor--Koniorczyk's question for the Fuchs--Caves measurement. -/
def claim : Prop :=
  ∀ (d : ℕ) (ρ σ : Matrix (Fin d) (Fin d) ℂ),
    ρ.PosDef → ρ.trace = 1 → σ.PosDef → σ.trace = 1 →
    ∀ a : Fin d → Fin d → ℂ,
      isOrderedFidelityEigenbasis ρ σ a →
      ∀ k : Fin (d + 1),
        onOptimalROC ρ σ (cumulativeFalsePositive ρ a k)
          (cumulativeTruePositive σ a k)

private noncomputable def rho : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 20 : ℝ) • !![2, 1, 1; 1, 10, 1; 1, 1, 8]

private noncomputable def sigma : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 40 : ℝ) • !![16, 4, 2; 4, 20, 1; 2, 1, 4]

private noncomputable def diagonal : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i : Fin 3 =>
    if i = 0 then (2 : ℂ) else if i = 1 then 1 else (1 / 2 : ℂ))

private noncomputable def coordinateBasis : Fin 3 → Fin 3 → ℂ :=
  fun i j => if i = j then 1 else 0

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
  have hstar : diagonalᴴ = diagonal := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [diagonal, Matrix.conjTranspose, Matrix.diagonal, RCLike.star_def,
        map_ofNat]
  simpa only [hstar] using hcong

private theorem sigma_trace : sigma.trace = 1 := by
  norm_num [sigma, Matrix.trace, Matrix.smul_apply, Fin.sum_univ_succ]

private theorem sqrt_observable : fidelityObservable rho sigma = diagonal := by
  let s : Matrix (Fin 3) (Fin 3) ℂ := CFC.sqrt rho
  have hsquare : s * s = rho := CFC.sqrt_mul_sqrt_self rho rho_posDef.posSemidef.nonneg
  have hsstar : sᴴ = s := (CFC.sqrt_nonneg rho).posSemidef.isHermitian.eq
  have hroot : (s * diagonal * s).PosSemidef := by
    simpa only [hsstar] using diagonal_posDef.posSemidef.mul_mul_conjTranspose_same s
  have hprod : (s * diagonal * s) * (s * diagonal * s) = s * sigma * s := by
    calc
      (s * diagonal * s) * (s * diagonal * s) =
          s * diagonal * (s * s) * diagonal * s := by noncomm_ring
      _ = s * diagonal * rho * diagonal * s := by rw [hsquare]
      _ = s * (diagonal * rho * diagonal) * s := by noncomm_ring
      _ = s * sigma * s := by rw [sigma_eq]
  have hsqrt : CFC.sqrt (s * sigma * s) = s * diagonal * s :=
    CFC.sqrt_unique hprod hroot.nonneg
  have hsunit : IsUnit s :=
    (CFC.isUnit_sqrt_iff rho rho_posDef.posSemidef.nonneg).mpr rho_posDef.isUnit
  have hsdet : IsUnit s.det := s.isUnit_iff_isUnit_det.mp hsunit
  have hleft : s⁻¹ * s = 1 := s.nonsing_inv_mul hsdet
  have hright : s * s⁻¹ = 1 := s.mul_nonsing_inv hsdet
  change s⁻¹ * CFC.sqrt (s * sigma * s) * s⁻¹ = diagonal
  rw [hsqrt]
  calc
    s⁻¹ * (s * diagonal * s) * s⁻¹ =
        (s⁻¹ * s) * diagonal * (s * s⁻¹) := by noncomm_ring
    _ = diagonal := by rw [hleft, hright]; simp

private theorem coordinate_basis_ordered :
    isOrderedFidelityEigenbasis rho sigma coordinateBasis := by
  unfold isOrderedFidelityEigenbasis
  rw [sqrt_observable]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      apply Complex.ext <;>
        norm_num [coordinateBasis, star, dotProduct, Fin.sum_univ_succ, RCLike.star_def,
          map_ofNat]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [coordinateBasis, star, dotProduct, Fin.sum_univ_succ, RCLike.star_def,
        map_ofNat, Complex.ext_iff]
  · intro i
    fin_cases i
    · refine ⟨2, ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, coordinateBasis, Matrix.mulVec, dotProduct, Matrix.diagonal,
          Matrix.of_apply, Complex.ext_iff, Fin.sum_univ_succ]
    · refine ⟨1, ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, coordinateBasis, Matrix.mulVec, dotProduct, Matrix.diagonal,
          Matrix.of_apply, Complex.ext_iff, Fin.sum_univ_succ]
    · refine ⟨(1 / 2 : ℝ), ?_⟩
      ext j
      fin_cases j <;>
        simp [diagonal, coordinateBasis, Matrix.mulVec, dotProduct, Matrix.diagonal,
          Matrix.of_apply, Complex.ext_iff, Fin.sum_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      try norm_num at hij
    all_goals
      norm_num [outcome, coordinateBasis, rho, sigma, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

private noncomputable def competitorVector : Fin 3 → ℂ := ![37, 2, -3]

private theorem competitor_eq :
    competitor = (1 / 1382 : ℝ) •
      Matrix.vecMulVec competitorVector (star competitorVector) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [competitor, competitorVector, Matrix.vecMulVec, Matrix.smul_apply,
      Pi.star_apply, RCLike.star_def, map_ofNat]

private theorem rank_one_upper (v : Fin 3 → ℂ) :
    (((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      Matrix.vecMulVec v (star v)).PosSemidef := by
  let t : ℝ := ∑ j, ‖v j‖ ^ 2
  have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs (x : Fin 3 → ℂ) :
      ‖star v ⬝ᵥ x‖ ^ 2 ≤ t * (∑ j, ‖x j‖ ^ 2) := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 v) (WithLp.toLp 2 x)
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply, t] using hsq
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr ht)).1.sub
      (Matrix.posSemidef_vecMulVec_self_star v).1) ?_
  intro x
  have hstar : star x ⬝ᵥ v = star (star v ⬝ᵥ x) := by
    exact star_dotProduct x v
  have heq : star x ⬝ᵥ (((t : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      Matrix.vecMulVec v (star v)) *ᵥ x) =
      ((t * (∑ j, ‖x j‖ ^ 2) - ‖star v ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
    have hnorm (y : Fin 3 → ℂ) :
        star y ⬝ᵥ y = ((∑ j, ‖y j‖ ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;>
        simp [dotProduct, RCLike.star_def, Complex.mul_re, Complex.mul_im,
          ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;> ring_nf <;> simp
    have hz : star (star v ⬝ᵥ x) * (star v ⬝ᵥ x) =
        ((‖star v ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, dotProduct_mulVec, Matrix.vecMul_vecMulVec,
      smul_dotProduct, smul_eq_mul, hstar]
    rw [hnorm x, hz]
    norm_num [Complex.ofReal_mul, Complex.ofReal_sub]
  rw [heq]
  exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hcs x))

private theorem competitor_binary : isBinaryTest competitor := by
  rw [isBinaryTest]
  constructor
  · rw [competitor_eq]
    exact ((Matrix.posSemidef_vecMulVec_self_star competitorVector).smul
      (by norm_num)).nonneg
  · apply Matrix.le_iff.mpr
    have hv : ∑ j, ‖competitorVector j‖ ^ 2 = (1382 : ℝ) := by
      norm_num [competitorVector, Fin.sum_univ_succ]
    have h := rank_one_upper competitorVector
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
    cumulativeFalsePositive rho coordinateBasis ⟨1, by decide⟩ = 1 / 10 := by
  change Finset.sum (Finset.univ.filter (fun i : Fin 3 => i.val < 1))
      (outcome coordinateBasis rho) = 1 / 10
  rw [show Finset.univ.filter (fun i : Fin 3 => i.val < 1) = {0} by decide]
  norm_num [outcome, coordinateBasis, rho, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

private theorem cumulative_first_sigma :
    cumulativeTruePositive sigma coordinateBasis ⟨1, by decide⟩ = 2 / 5 := by
  change Finset.sum (Finset.univ.filter (fun i : Fin 3 => i.val < 1))
      (outcome coordinateBasis sigma) = 2 / 5
  rw [show Finset.univ.filter (fun i : Fin 3 => i.val < 1) = {0} by decide]
  norm_num [outcome, coordinateBasis, sigma, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.smul_apply, Complex.mul_re, Complex.mul_im]

/-- The preregistered three-dimensional witness refutes the open question. -/
theorem result : ¬ claim := by
  intro h
  have hroc := h 3 rho sigma rho_posDef rho_trace sigma_posDef sigma_trace
    coordinateBasis coordinate_basis_ordered ⟨1, by decide⟩
  have hle := hroc competitor competitor_binary (by
    rw [competitor_rho_trace, cumulative_first_rho])
  rw [competitor_sigma_trace, cumulative_first_sigma] at hle
  norm_num at hle

end D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation
