/- GID: D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The calibrated separable two-qubit CHSH value is attained and optimal. -/

import D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
import D5.S3.Quantum.Information.ActualPureQubitGeometry

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.NonlocalityDepthQuantumBound (IsBinaryObservable)
open D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness (Separable)

namespace D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum

/-- The real expectation of the CHSH operator on two qubits. -/
def witness (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (trace (ρ * (a₁ ⊗ₖ b₁ + a₁ ⊗ₖ b₂ + a₂ ⊗ₖ b₁ - a₂ ⊗ₖ b₂))).re

/-- Four binary observables calibrated against the Pauli X and Z targets. -/
def Admissible (ε : ℝ) (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsBinaryObservable a₁ ∧ IsBinaryObservable a₂ ∧
  IsBinaryObservable b₁ ∧ IsBinaryObservable b₂ ∧
  2 - 4 * ε ≤ (trace (a₁ * qubitX)).re ∧
  2 - 4 * ε ≤ (trace (a₂ * qubitZ)).re ∧
  2 - 4 * ε ≤ (trace (b₁ * qubitX)).re ∧
  2 - 4 * ε ≤ (trace (b₂ * qubitZ)).re

/-- The sharp separable value, with its constant branch past the calibration threshold. -/
def separableValue (ε : ℝ) : ℝ :=
  if ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2) then
    4 * (1 - 2 * ε) * Real.sqrt (ε * (1 - ε)) +
      Real.sqrt (2 - 16 * ε * (1 - ε) * (1 - 2 * ε) ^ 2)
  else 2

/-- The sharp value is a greatest element of the full set of admissible witness values. -/
def claim : Prop :=
  ∀ ε ∈ Set.Icc (0 : ℝ) 1,
    IsGreatest {w | ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧
      Admissible ε a₁ a₂ b₁ b₂ ∧ w = witness ρ a₁ a₂ b₁ b₂} (separableValue ε)

private lemma product_upper_small (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2))
    (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1)
    (ha : Admissible ε a₁ a₂ b₁ b₂) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ separableValue ε := by
  sorry

private lemma product_upper_two (σ τ a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ)
    (hσ : σ.PosSemidef) (htσ : trace σ = 1)
    (hτ : τ.PosSemidef) (htτ : trace τ = 1)
    (ha₁ : IsBinaryObservable a₁) (ha₂ : IsBinaryObservable a₂)
    (hb₁ : IsBinaryObservable b₁) (hb₂ : IsBinaryObservable b₂) :
    witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ 2 := by
  sorry

private lemma convex_extension (a₁ a₂ b₁ b₂ : Matrix (Fin 2) (Fin 2) ℂ) (v : ℝ)
    (h : ∀ σ τ : Matrix (Fin 2) (Fin 2) ℂ,
      σ.PosSemidef → trace σ = 1 → τ.PosSemidef → trace τ = 1 →
      witness (σ ⊗ₖ τ) a₁ a₂ b₁ b₂ ≤ v)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : Separable ρ) :
    witness ρ a₁ a₂ b₁ b₂ ≤ v := by
  sorry

private lemma attainment_small (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)
    (hsmall : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)) :
    ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧ Admissible ε a₁ a₂ b₁ b₂ ∧
      separableValue ε = witness ρ a₁ a₂ b₁ b₂ := by
  sorry

private lemma attainment_large (ε : ℝ)
    (hlarge : 1 / 2 - 1 / (2 * Real.sqrt 2) < ε) :
    ∃ ρ a₁ a₂ b₁ b₂, Separable ρ ∧ Admissible ε a₁ a₂ b₁ b₂ ∧
      separableValue ε = witness ρ a₁ a₂ b₁ b₂ := by
  sorry

theorem result : claim := by
  intro ε hε
  constructor
  · by_cases hs : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)
    · exact attainment_small ε hε hs
    · exact attainment_large ε (lt_of_not_ge hs)
  · rintro w ⟨ρ, a₁, a₂, b₁, b₂, hρ, ha, rfl⟩
    apply convex_extension a₁ a₂ b₁ b₂ (separableValue ε) _ ρ hρ
    intro σ τ hσ htσ hτ htτ
    by_cases hs : ε ≤ 1 / 2 - 1 / (2 * Real.sqrt 2)
    · exact product_upper_small ε hε hs σ τ a₁ a₂ b₁ b₂ hσ htσ hτ htτ ha
    · rw [separableValue, if_neg hs]
      exact product_upper_two σ τ a₁ a₂ b₁ b₂ hσ htσ hτ htτ
        ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1

end D5.S3.QuantumBounds.ImpreciseCHSHSeparableOptimum
