/- GID: D5/S3/Entropy/UnifiedEntropyTriangleRefutation
   generality: I
   mirror-B: D5/B/S3/Entropy/UnifiedEntropyTriangleRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim; result=D5/S3/Entropy/UnifiedEntropyTriangleRefutation.result; claim=D5/S3/Entropy/UnifiedEntropyTriangleRefutation.claim
   digest: Unified entropy correlations violate the triangle inequality at (2, -1). -/

import D5.S3.Quantum.Information.ActualPureQubitGeometry
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

open scoped BigOperators Kronecker ComplexOrder
open Matrix
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Entropy.UnifiedEntropyTriangleRefutation

/-- Spectral power trace, with real powers on the spectrum. -/
def genPurity {α : Type} [Fintype α] [DecidableEq α]
    (q : ℝ) (σ : Matrix α α ℂ) : ℝ :=
  (cfc (fun x : ℝ => x ^ q) σ).trace.re

/-- Unified entropy away from its limiting indices. -/
def unifiedEntropy {α : Type} [Fintype α] [DecidableEq α]
    (q s : ℝ) (σ : Matrix α α ℂ) : ℝ :=
  (genPurity q σ ^ s - 1) / ((1 - q) * s)

/-- The rank-one projector on a column of a unitary matrix. -/
def projector {α : Type} [Fintype α] [DecidableEq α]
    (u : Matrix.unitaryGroup α ℂ) (i : α) : Matrix α α ℂ :=
  fun a b => u a i * star (u b i)

/-- Unread rank-one projective measurement on the first factor. -/
def measureA {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : Matrix.unitaryGroup α ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :=
  ∑ i, (projector u i ⊗ₖ (1 : Matrix β β ℂ)) * ρ * (projector u i ⊗ₖ 1)

/-- Unread rank-one projective measurement on the second factor. -/
def measureB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (v : Matrix.unitaryGroup β ℂ) (ρ : Matrix (α × β) (α × β) ℂ) :=
  ∑ j, ((1 : Matrix α α ℂ) ⊗ₖ projector v j) * ρ * (1 ⊗ₖ projector v j)

/-- Unread local rank-one projective measurement on both factors. -/
def measureAB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (u : Matrix.unitaryGroup α ℂ) (v : Matrix.unitaryGroup β ℂ)
    (ρ : Matrix (α × β) (α × β) ℂ) :=
  ∑ i, ∑ j, (projector u i ⊗ₖ projector v j) * ρ * (projector u i ⊗ₖ projector v j)

/-- Entropic disturbance normalized by the original spectral power trace. -/
def disturbance {α : Type} [Fintype α] [DecidableEq α]
    (q s : ℝ) (σ ρ : Matrix α α ℂ) : ℝ :=
  (unifiedEntropy q s σ - unifiedEntropy q s ρ) / genPurity q ρ ^ s

/-- Infimum over every local measurement on the first factor. -/
def correlationA {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun u : Matrix.unitaryGroup α ℂ => disturbance q s (measureA u ρ) ρ)

/-- Infimum over every local measurement on the second factor. -/
def correlationB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun v : Matrix.unitaryGroup β ℂ => disturbance q s (measureB v ρ) ρ)

/-- Infimum over all pairs of local rank-one measurements. -/
def correlationAB {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q s : ℝ) (ρ : Matrix (α × β) (α × β) ℂ) : ℝ :=
  sInf (Set.range fun uv : Matrix.unitaryGroup α ℂ × Matrix.unitaryGroup β ℂ =>
    disturbance q s (measureAB uv.1 uv.2 ρ) ρ)

/-- The triangle-like inequality for every admissible unified entropy and finite state. -/
def claim : Prop :=
  ∀ q s : ℝ, 0 < q → q ≠ 1 → s ≠ 0 →
    ∀ (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      (ρ : Matrix (α × β) (α × β) ℂ),
      ρ.PosSemidef → ρ.trace = 1 →
      correlationAB q s ρ ≤ correlationA q s ρ + correlationB q s ρ

private def witness : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a b =>
    ( !![!![6, 1; 1, 2], !![1, 0; 0, 1];
         !![1, 0; 0, 1], !![2, 1; 1, 6]] :
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℂ)) a.1 b.1 a.2 b.2 / 16

private lemma witness_posSemidef : witness.PosSemidef := by
  sorry

private lemma witness_trace : witness.trace = 1 := by
  sorry

private lemma witness_purity : (witness * witness).trace.re = 11 / 32 := by
  sorry

private lemma genPurity_two {α : Type} [Fintype α] [DecidableEq α]
    (σ : Matrix α α ℂ) (hσ : σ.IsHermitian) :
    genPurity 2 σ = (σ * σ).trace.re := by
  sorry

private lemma disturbance_two_neg_one {α : Type} [Fintype α] [DecidableEq α]
    (σ ρ : Matrix α α ℂ) (hσ : σ.IsHermitian) (hρ : ρ.IsHermitian)
    (hp : (ρ * ρ).trace.re ≠ 0) :
    disturbance 2 (-1) σ ρ = (ρ * ρ).trace.re / (σ * σ).trace.re - 1 := by
  sorry

private lemma qubit_projectors (u : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧
      projector u 0 = blochMatrix 1 n ∧ projector u 1 = 1 - projector u 0 := by
  sorry

private lemma measured_hermitian (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    (measureA u witness).IsHermitian ∧ (measureB v witness).IsHermitian ∧
      (measureAB u v witness).IsHermitian := by
  sorry

private lemma measured_purities (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ n m : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧ ‖m‖ = 1 ∧
      (measureA u witness * measureA u witness).trace.re =
        (1 + 1 / 16 + (n 0)^2 / 16 + (n 2)^2 / 4) / 4 ∧
      (measureB v witness * measureB v witness).trace.re =
        (1 + 1 / 16 + (m 0)^2 / 16 + (m 2)^2 / 4) / 4 ∧
      (measureAB u v witness * measureAB u v witness).trace.re =
        (1 + ((n 0)^2 + (m 0)^2) / 16 + (n 2)^2 * (m 2)^2 / 4) / 4 := by
  sorry

private lemma measured_purity_bounds (u v : Matrix.unitaryGroup (Fin 2) ℂ) :
    (1 / 4 ≤ (measureA u witness * measureA u witness).trace.re ∧
      (measureA u witness * measureA u witness).trace.re ≤ 21 / 64) ∧
    (1 / 4 ≤ (measureB v witness * measureB v witness).trace.re ∧
      (measureB v witness * measureB v witness).trace.re ≤ 21 / 64) ∧
    (1 / 4 ≤ (measureAB u v witness * measureAB u v witness).trace.re ∧
      (measureAB u v witness * measureAB u v witness).trace.re ≤ 5 / 16) := by
  sorry

private lemma computational_purities :
    (measureA 1 witness * measureA 1 witness).trace.re = 21 / 64 ∧
    (measureB 1 witness * measureB 1 witness).trace.re = 21 / 64 ∧
    (measureAB 1 1 witness * measureAB 1 1 witness).trace.re = 5 / 16 := by
  sorry

private lemma correlations : correlationA 2 (-1) witness = 1 / 21 ∧
    correlationB 2 (-1) witness = 1 / 21 ∧ correlationAB 2 (-1) witness = 1 / 10 := by
  sorry

/-- The two-qubit rational state refutes universal validity of the inequality. -/
theorem result : ¬ claim := by
  intro h
  have hv := h 2 (-1) (by norm_num) (by norm_num) (by norm_num)
    (Fin 2) (Fin 2) witness witness_posSemidef witness_trace
  obtain ⟨ha, hb, hab⟩ := correlations
  rw [ha, hb, hab] at hv
  norm_num at hv

end D5.S3.Entropy.UnifiedEntropyTriangleRefutation
