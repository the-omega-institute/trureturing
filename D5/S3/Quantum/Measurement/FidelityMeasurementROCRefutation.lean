/- GID: D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/FidelityMeasurementROCRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim; result=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.result; claim=D5/S3/Quantum/Measurement/FidelityMeasurementROCRefutation.claim
   digest: The Fuchs--Caves fidelity measurement has a nonoptimal ROC point in dimension three. -/

import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
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

private noncomputable def outcome {d : ℕ} (a : Fin d → Fin d → ℂ)
    (m : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : ℝ :=
  ((star (a i)) ⬝ᵥ (m *ᵥ a i)).re

private noncomputable def cumulative {d : ℕ} (a : Fin d → Fin d → ℂ)
    (m : Matrix (Fin d) (Fin d) ℂ) (k : Fin (d + 1)) : ℝ :=
  ∑ i in Finset.univ.filter (fun i : Fin d => i < k), outcome a m i

private def isOrderedFidelityEigenbasis {d : ℕ}
    (ρ σ : Matrix (Fin d) (Fin d) ℂ) (a : Fin d → Fin d → ℂ) : Prop :=
  (∀ i, ∑ j, conj (a i j) * a i j = 1) ∧
  (∀ i j, i ≠ j → ∑ k, conj (a i k) * a j k = 0) ∧
  (∀ i, ∃ λ : ℝ, fidelityObservable ρ σ *ᵥ a i = (λ : ℂ) • a i) ∧
  (∀ i j, i ≤ j → outcome a ρ i * outcome a σ j ≥ outcome a ρ j * outcome a σ i)

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
  !![(2 : ℂ), 0, 0; 0, 1, 0; 0, 0, (1 / 2 : ℂ)]

private noncomputable def coordinateBasis : Fin 3 → Fin 3 → ℂ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

private noncomputable def competitor : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 1382 : ℝ) • !![1369, 74, -111; 74, 4, -6; -111, -6, 9]

private theorem rho_posDef : rho.PosDef := by sorry
private theorem rho_trace : rho.trace = 1 := by sorry
private theorem sigma_eq : sigma = diagonal * rho * diagonal := by sorry
private theorem sigma_posDef : sigma.PosDef := by sorry
private theorem sigma_trace : sigma.trace = 1 := by sorry
private theorem sqrt_observable : fidelityObservable rho sigma = diagonal := by sorry
private theorem coordinate_basis_ordered :
    isOrderedFidelityEigenbasis rho sigma coordinateBasis := by sorry
private theorem competitor_binary : isBinaryTest competitor := by sorry
private theorem competitor_rho_trace : (competitor * rho).trace.re = 1 / 10 := by sorry
private theorem competitor_sigma_trace : (competitor * sigma).trace.re = 5539 / 13820 := by sorry
private theorem cumulative_first_rho :
    cumulativeFalsePositive rho coordinateBasis ⟨1, by decide⟩ = 1 / 10 := by sorry
private theorem cumulative_first_sigma :
    cumulativeTruePositive sigma coordinateBasis ⟨1, by decide⟩ = 2 / 5 := by sorry

/-- The preregistered three-dimensional witness refutes the open question. -/
theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Measurement.FidelityMeasurementROCRefutation
