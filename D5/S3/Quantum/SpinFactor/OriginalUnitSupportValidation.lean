import D5.S3.Quantum.SpinFactor.OriginalUnitSupport

open D5.S3.Quantum.SpinFactor.OriginalUnitSupport
open scoped Matrix ComplexOrder

noncomputable section

private def realS : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := LinearMap.mul ℝ ℝ
private def realD (_ _ : ℝ) : ℝ := 0
private def realP : Set (ℝ →ₗ[ℝ] ℝ) := {LinearMap.id}

example : P2 realS realD realP := by
  intro α hα a b
  simp only [realP, Set.mem_singleton_iff] at hα
  subst α
  convert Matrix.posSemidef_vecMulVec_self_star (![a, b] : Fin 2 → ℂ) using 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [table, realS, realD, Matrix.vecMulVec]

example : PB realS realD realP := by
  intro α hα a b c
  simp only [realP, Set.mem_singleton_iff] at hα
  subst α
  simp [squareReadout, realS, realD]
  ring

example : (∀ x y, realS x y = realS y x) ∧
    (∀ x, realS 1 x = x) ∧ (∀ x, ‖realS x x‖ = ‖x‖ ^ 2) ∧
    (∀ x, (∀ α ∈ realP, α x = 0) → x = 0) ∧
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1 = 1 ∧
    (∀ x : ℝ, |(LinearMap.id : ℝ →ₗ[ℝ] ℝ) x| ≤ ‖x‖) ∧
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ) ∈ realP) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro x y; exact mul_comm x y
  · intro x; exact one_mul x
  · intro x; simp [realS, Real.norm_eq_abs, abs_mul, pow_two]
  · intro x hx; exact hx LinearMap.id (by simp [realP])
  · intro x; exact le_rfl
  · simp [realP]

example : (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (realD 2 3) = 0 ∧
    |(0 : ℝ)| = ‖realD 2 3‖ := by simp [realD]

example : ¬ ∃ Z : ℝ, Z ≠ 0 ∧
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (realD 2 3) = Z ∧ |Z| = ‖realD 2 3‖ := by
  simp [realD]

#print axioms D5.S3.Topology.OrderUnitNorm.Data.positive_norm_support
#print axioms positive_support_unit_boundary
#print axioms unit_row_closed_ball
#print axioms unit_row_semidefinite
#check @unit_row_semidefinite
#check @positive_support_unit_boundary
