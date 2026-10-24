/- GID: D5/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/UnifiedImaginarityMonotoneComparison
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unified imaginarity minimized over real states is bounded by conjugate divergence. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

local notation "IsState" => IsDensity
local instance {d : ℕ} : Pow (Matrix (Fin d) (Fin d) ℂ) ℝ := ⟨CFC.rpow⟩

/-- Entrywise conjugation in the fixed computational basis. -/
def conj {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ρ.map star

/-- The unified relative entropy for real parameters. -/
def unifiedDivergence {d : ℕ} (α β : ℝ) (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (((ρ ^ α * σ ^ (1 - α)).trace.re) ^ β - 1) / ((α - 1) * β)

/-- Imaginarity measured by divergence from the conjugate state. -/
def imaginarityH {d : ℕ} (α β : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  unifiedDivergence α β ρ (conj ρ)

/-- Imaginarity measured by the infimum of divergences from real states. -/
def imaginarityE {d : ℕ} (α β : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf {x | ∃ σ, IsState σ ∧ conj σ = σ ∧ x = unifiedDivergence α β ρ σ}

/-- The comparison includes every finite positive dimension and singular density matrices. -/
def claim : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsState ρ →
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioc (0 : ℝ) 1,
      imaginarityE α β ρ ≤ imaginarityH α β ρ

variable {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ} {α β : ℝ}

private def realCompetitor (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • (ρ + conj ρ)

private lemma conjugate_state (hρ : IsState ρ) : IsState (conj ρ) := by
  sorry

private lemma real_competitor (hρ : IsState ρ) :
    IsState (realCompetitor ρ) ∧ conj (realCompetitor ρ) = realCompetitor ρ := by
  sorry

private lemma overlap_nonneg (ρ σ : Matrix (Fin d) (Fin d) ℂ) (α : ℝ) :
    0 ≤ (ρ ^ α * σ ^ (1 - α)).trace.re := by
  sorry

private lemma overlap_le_one (hρ : IsState ρ) (hσ : IsState σ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (ρ ^ α * σ ^ (1 - α)).trace.re ≤ 1 := by
  sorry

private lemma midpoint_overlap (hρ : IsState ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    (1 + (ρ ^ α * (conj ρ) ^ (1 - α)).trace.re) / 2 ≤
      (ρ ^ α * (realCompetitor ρ) ^ (1 - α)).trace.re := by
  sorry

private lemma scalar_midpoint {q r : ℝ} (hq : 0 ≤ q) (hr : (1 + q) / 2 ≤ r)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    (1 + q ^ β) / 2 ≤ r ^ β := by
  sorry

private lemma divergence_nonneg (hρ : IsState ρ) (hσ : IsState σ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ unifiedDivergence α β ρ σ := by
  sorry

private lemma competitor_half (hρ : IsState ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    unifiedDivergence α β ρ (realCompetitor ρ) ≤ imaginarityH α β ρ / 2 := by
  sorry

private lemma values_bddBelow (hρ : IsState ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    BddBelow {x | ∃ σ, IsState σ ∧ conj σ = σ ∧ x = unifiedDivergence α β ρ σ} := by
  refine ⟨0, ?_⟩
  rintro x ⟨σ, hσ, _, rfl⟩
  exact divergence_nonneg hρ hσ hα hβ

private lemma inf_le_competitor (hρ : IsState ρ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hβ : β ∈ Set.Ioc (0 : ℝ) 1) :
    imaginarityE α β ρ ≤ unifiedDivergence α β ρ (realCompetitor ρ) := by
  apply csInf_le (values_bddBelow hρ hα hβ)
  exact ⟨realCompetitor ρ, (real_competitor hρ).1, (real_competitor hρ).2, rfl⟩

/-- The real part of a state supplies a competitor with at most half the conjugate divergence. -/
theorem result : claim := by
  intro d _ ρ hρ α hα β hβ
  have hH : 0 ≤ imaginarityH α β ρ :=
    divergence_nonneg hρ (conjugate_state hρ) hα hβ
  calc
    imaginarityE α β ρ ≤ unifiedDivergence α β ρ (realCompetitor ρ) :=
      inf_le_competitor hρ hα hβ
    _ ≤ imaginarityH α β ρ / 2 := competitor_half hρ hα hβ
    _ ≤ imaginarityH α β ρ := by linarith

end D5.S3.Quantum.Divergence.UnifiedImaginarityMonotoneComparison
