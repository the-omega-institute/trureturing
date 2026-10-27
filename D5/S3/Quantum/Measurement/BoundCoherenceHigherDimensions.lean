/- GID: D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/BoundCoherenceHigherDimensions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bound coherent states exist in every dimension at least three. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section

namespace D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions

open scoped BigOperators Kronecker Matrix ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation

/-- The truncated number observable on a system of dimension `d`. -/
def numberOp (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun n => (n.val : ℂ)

/-- An allowed unitary conserves the sum of the two local number observables. -/
def IsAllowedUnitary {d : ℕ} (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Prop :=
  v ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
    v * (numberOp d ⊗ₖ 1 + 1 ⊗ₖ numberOp d) =
      (numberOp d ⊗ₖ 1 + 1 ⊗ₖ numberOp d) * v

/-- The matrix entries with the specified signed number difference. -/
def mode {d : ℕ} (j : ℤ) (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun r s => if (r.val : ℤ) - s.val = j then ρ r s else 0

/-- Coherence in one mode is the trace norm of that mode. -/
def modeCoherence {d : ℕ} (j : ℤ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  traceNorm (mode j ρ)

/-- The first marginal after an allowed interaction of two identical input copies. -/
def concentrated {d : ℕ} (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  partialTraceRight (v * (ρ ⊗ₖ ρ) * vᴴ)

/-- A maximally coherent pure state has equal modulus in every number eigenvector. -/
def IsMaximallyCoherent {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ θ : Fin d → ℝ,
    ρ = Matrix.vecMulVec
      (fun n => Complex.exp (θ n * Complex.I) / (Real.sqrt d : ℂ))
      (star (fun n => Complex.exp (θ n * Complex.I) / (Real.sqrt d : ℂ)))

/-- Every dimension at least three admits a coherent, nonmaximal state whose every
positive mode fails to increase under any allowed two-copy unitary. -/
def claim : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ ρ : Matrix (Fin d) (Fin d) ℂ,
    ρ.PosSemidef ∧ ρ.trace = 1 ∧ ρ * numberOp d ≠ numberOp d * ρ ∧
      ¬ IsMaximallyCoherent ρ ∧
      ∀ v, IsAllowedUnitary v → ∀ j : ℕ, 1 ≤ j → j ≤ d - 1 →
        modeCoherence j (concentrated v ρ) ≤ modeCoherence j ρ

private def witness (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun r s => (d : ℂ)⁻¹ * ((if r = s then 1 else 0) +
    (if r.val = d - 1 ∧ s.val = 0 then 1 else 0) +
    (if r.val = 0 ∧ s.val = d - 1 then 1 else 0))

private theorem concentrated_last_entry_bound {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v) :
    ‖concentrated v (witness d) ⟨d - 1, by omega⟩ ⟨0, by omega⟩‖ ≤ (d : ℝ)⁻¹ := by
  sorry

private theorem witness_posSemidef {d : ℕ} (hd : 3 ≤ d) :
    (witness d).PosSemidef := by
  sorry

private theorem witness_trace {d : ℕ} (hd : 3 ≤ d) : (witness d).trace = 1 := by
  sorry

private theorem witness_coherent {d : ℕ} (hd : 3 ≤ d) :
    witness d * numberOp d ≠ numberOp d * witness d := by
  sorry

private theorem witness_not_maximal {d : ℕ} (hd : 3 ≤ d) :
    ¬ IsMaximallyCoherent (witness d) := by
  sorry

private theorem concentrated_lower_mode {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j < d - 1) :
    mode (j : ℤ) (concentrated v (witness d)) = 0 := by
  sorry

private theorem last_mode_traceNorm {d : ℕ} (hd : 3 ≤ d)
    (x : Matrix (Fin d) (Fin d) ℂ) :
    modeCoherence (d - 1 : ℕ) x = ‖x ⟨d - 1, by omega⟩ ⟨0, by omega⟩‖ := by
  sorry

private theorem witness_last_coherence {d : ℕ} (hd : 3 ≤ d) :
    modeCoherence (d - 1 : ℕ) (witness d) = (d : ℝ)⁻¹ := by
  rw [last_mode_traceNorm hd]
  sorry

private theorem witness_no_concentration {d : ℕ} (hd : 3 ≤ d)
    (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hv : IsAllowedUnitary v)
    (j : ℕ) (hj : 1 ≤ j) (hjd : j ≤ d - 1) :
    modeCoherence j (concentrated v (witness d)) ≤ modeCoherence j (witness d) := by
  rcases hjd.eq_or_lt with h | h
  · subst j
    rw [last_mode_traceNorm hd, witness_last_coherence hd]
    exact concentrated_last_entry_bound hd v hv
  · rw [modeCoherence, concentrated_lower_mode hd v hv j hj h]
    have hz : traceNorm (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
      sorry
    rw [hz]
    exact traceNorm_nonneg _

theorem result : claim := by
  intro d hd
  exact ⟨witness d, witness_posSemidef hd, witness_trace hd, witness_coherent hd,
    witness_not_maximal hd, fun v hv j hj hjd => witness_no_concentration hd v hv j hj hjd⟩

end D5.S3.Quantum.Measurement.BoundCoherenceHigherDimensions
