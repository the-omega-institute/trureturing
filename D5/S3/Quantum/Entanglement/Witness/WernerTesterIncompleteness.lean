/- GID: D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim; result=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.result; claim=D5/S3/Quantum/Entanglement/Witness/WernerTesterIncompleteness.claim
   digest: Entangled Werner states need not be detected by any pair of complex testers. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness

noncomputable section

/-- A complex tester has trace-norm to Euclidean operator norm exactly one. -/
def IsTester {d n : ℕ}
    (e : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : Prop :=
  (∀ x, ‖e x‖ ≤ traceNorm x) ∧ ∃ x, x ≠ 0 ∧ ‖e x‖ = traceNorm x

/-- The coefficient matrix of the tensor product of two complex linear maps. -/
def testerImage {d₁ d₂ n₁ n₂ : ℕ}
    (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    Matrix (Fin n₁) (Fin n₂) ℂ :=
  fun p q => ∑ i, ∑ j, ∑ k, ∑ l,
    ρ (i, j) (k, l) * e₁ (Matrix.single i k 1) p * e₂ (Matrix.single j l 1) q

/-- The projective tensor norm, as an infimum over all finite decompositions. -/
def projNorm {n₁ n₂ : ℕ} (m : Matrix (Fin n₁) (Fin n₂) ℂ) : ℝ :=
  sInf {r | ∃ (k : ℕ) (a : Fin k → EuclideanSpace ℂ (Fin n₁))
    (b : Fin k → EuclideanSpace ℂ (Fin n₂)),
    m = ∑ t, Matrix.of (fun p q => a t p * b t q) ∧ r = ∑ t, ‖a t‖ * ‖b t‖}

/-- Separable density matrices form the convex hull of all product density matrices. -/
def Separable {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) : Prop :=
  ρ ∈ convexHull ℝ {σ | ∃ (ρ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ρ₂ : Matrix (Fin d₂) (Fin d₂) ℂ),
    ρ₁.PosSemidef ∧ ρ₁.trace = 1 ∧ ρ₂.PosSemidef ∧ ρ₂.trace = 1 ∧
    σ = Matrix.kroneckerMap (· * ·) ρ₁ ρ₂}

/-- Werner's symmetric and antisymmetric mixture, with the flip on the two factors. -/
def werner (d : ℕ) (μ : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (μ / ((d : ℝ) * (d + 1))) •
      (1 + (Equiv.prodComm (Fin d) (Fin d)).permMatrix ℂ) +
    ((1 - μ) / ((d : ℝ) * (d - 1))) •
      (1 - (Equiv.prodComm (Fin d) (Fin d)).permMatrix ℂ)

/-- The bipartite completeness question for complex testers without index permutations. -/
def claim : Prop :=
  ∀ (d₁ d₂ : ℕ) (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ),
    ρ.PosSemidef → ρ.trace = 1 → ¬ Separable ρ →
    ∃ (n₁ n₂ : ℕ)
      (e₁ : Matrix (Fin d₁) (Fin d₁) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
      (e₂ : Matrix (Fin d₂) (Fin d₂) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂)),
      IsTester e₁ ∧ IsTester e₂ ∧ 1 < projNorm (testerImage e₁ e₂ ρ)

private theorem witness_pos : (werner 3 (1 / 3)).PosSemidef := by
  sorry

private theorem witness_trace : (werner 3 (1 / 3)).trace = 1 := by
  sorry

private theorem witness_entangled : ¬ Separable (werner 3 (1 / 3)) := by
  sorry

private theorem witness_bound {n₁ n₂ : ℕ}
    (e₁ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
    (e₂ : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂))
    (h₁ : ∀ x, ‖e₁ x‖ ≤ traceNorm x) (h₂ : ∀ x, ‖e₂ x‖ ≤ traceNorm x) :
    projNorm (testerImage e₁ e₂ (werner 3 (1 / 3))) ≤ 1 := by
  sorry

/-- The qutrit Werner state at parameter one third refutes tester completeness. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨n₁, n₂, e₁, e₂, h₁, h₂, hdet⟩ :=
    h 3 3 (werner 3 (1 / 3)) witness_pos witness_trace witness_entangled
  exact (not_lt_of_ge (witness_bound e₁ e₂ h₁.1 h₂.1)) hdet

end D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
