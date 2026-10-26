/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/Cap4FiniteChargeBudget
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Original finite head charge and norm budgets for uniform tail interpolation. -/
/- Weighted head norm and rank-one charge budgets for the complete
actual uniform coercivity comparison. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.Cap4FinitePerturbation
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixActualCoordinates

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Cap4FinitePerturbation
open Cap4FiniteCertificate

private theorem head_weight_bounds (i : I) : 0 ≤ weights i ∧ weights i ≤ 1 := by
  fin_cases i <;> norm_num [weights, weightsQ]

/-- The literal certificate weights cost at most the unweighted head norm. -/
theorem head_weighted_norm_le (u : I → ℝ) :
    (∑ i, weights i * u i ^ 2) ≤ ∑ i, u i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (head_weight_bounds i).2 (sq_nonneg (u i))

/-- Weighted Cauchy for exactly the original sixteen head coordinates. -/
theorem head_charge_sq_budget (u : I → ℝ) :
    (∑ i, weights i * u i) ^ 2 ≤ 16 * ∑ i, weights i * u i ^ 2 := by
  have hN : 0 ≤ ∑ i, weights i * u i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (head_weight_bounds i).1 (sq_nonneg _))
  have hW : (∑ i : I, weights i) ≤ 16 := by
    calc
      _ ≤ ∑ _i : I, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (head_weight_bounds i).2)
      _ = 16 := by simp [I]
  calc
    _ ≤ (∑ i, weights i) * ∑ i, weights i * u i ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
        (fun i _ => (head_weight_bounds i).1)
        (fun i _ => mul_nonneg (head_weight_bounds i).1 (sq_nonneg _))
      intro i _
      exact le_of_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right hW hN

/-- The same rank-one charge is paid by 3200 weighted head norms. -/
theorem head_charge_budget (u : I → ℝ) :
    rho * (∑ i, weights i * u i) ^ 2 ≤
      3200 * ∑ i, weights i * u i ^ 2 := by
  have hN : 0 ≤ ∑ i, weights i * u i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (head_weight_bounds i).1 (sq_nonneg _))
  have hq := head_charge_sq_budget u
  have hrho : 0 ≤ rho := by norm_num [rho, rhoQ]
  have hrho200 : rho ≤ 200 := by norm_num [rho, rhoQ]
  calc
    _ ≤ rho * (16 * ∑ i, weights i * u i ^ 2) :=
      mul_le_mul_of_nonneg_left hq hrho
    _ ≤ 200 * (16 * ∑ i, weights i * u i ^ 2) :=
      mul_le_mul_of_nonneg_right hrho200 (mul_nonneg (by norm_num) hN)
    _ = _ := by ring

end Cap4FinitePerturbation

namespace FiniteGaussianCap475
open FiniteGaussianCap4

/-- Actual normalized head norm is bounded by the unweighted charge-coordinate norm. -/
theorem actual_head_norm_le_coordinates (d : ℕ → ℝ) :
    (∑ k ∈ Finset.range 16, d k ^ 2) ≤
      ∑ i : Fin 16, (d i.val / actualMellinScale i.val) ^ 2 := by
  rw [certificate_head_norm_coordinates]
  exact Cap4FinitePerturbation.head_weighted_norm_le _

/-- Original rho and the same actual central charge. -/
theorem actual_head_charge_budget (d : ℕ → ℝ) :
    FiniteGaussianCap4.rho *
      (∑ k ∈ Finset.range 16, actualMellinScale k * d k) ^ 2 ≤
      3200 * ∑ k ∈ Finset.range 16, d k ^ 2 := by
  have hrho : Cap4FinitePerturbation.rho = FiniteGaussianCap4.rho := by
    norm_num [Cap4FinitePerturbation.rho, Cap4FiniteCertificate.rhoQ, FiniteGaussianCap4.rho]
  rw [certificate_head_charge_coordinates, certificate_head_norm_coordinates, ← hrho]
  exact Cap4FinitePerturbation.head_charge_budget _

end FiniteGaussianCap475
