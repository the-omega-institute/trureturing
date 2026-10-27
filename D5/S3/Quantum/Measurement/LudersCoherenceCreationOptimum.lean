/- GID: D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/LudersCoherenceCreationOptimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: General qubit measurements attain half the sum of coherence and Bloch length. -/

import D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation (l1Coherence)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum

/-- The nonselective measurement with the positive square roots of its effects. -/
def luders {n : ℕ} (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i, CFC.sqrt (e i) * ρ * CFC.sqrt (e i)

/-- The length of the Bloch vector in the computational basis. -/
def blochNorm (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt ((ρ 0 0 - ρ 1 1).re ^ 2 + 4 * ‖ρ 0 1‖ ^ 2)

private theorem coherence_two (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.IsHermitian) :
    l1Coherence ρ = 2 * ‖ρ 0 1‖ := by
  sorry

private theorem luders_decomposition {n : ℕ} (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : IsDensity ρ) (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (he : IsPOVM e) :
    ∃ (k : Fin n → ℝ) (z : Fin n → ℂ) (v : Fin n → ℝ),
      (∀ i, 0 ≤ k i) ∧ (∑ i, k i + 2 * (‖z i‖ ^ 2 + v i ^ 2)) = 1 ∧
      (luders e ρ).IsHermitian ∧
      (luders e ρ) 0 1 = ∑ i, (k i : ℂ) * ρ 0 1 +
        ((2 * (star (z i) * ρ 0 1).re + v i * (ρ 0 0 - ρ 1 1).re : ℝ) : ℂ) * z i := by
  sorry

private theorem dephasing_bound (c z : ℂ) (v r : ℝ) :
    2 * ‖((2 * (star z * c).re + v * r : ℝ) : ℂ) * z‖ ≤
      (‖z‖ ^ 2 + v ^ 2) * (2 * ‖c‖ + Real.sqrt (r ^ 2 + 4 * ‖c‖ ^ 2)) := by
  sorry

private theorem measurement_bound {n : ℕ} (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (hρ : IsDensity ρ) (e : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (he : IsPOVM e) :
    l1Coherence (luders e ρ) ≤ (l1Coherence ρ + blochNorm ρ) / 2 := by
  obtain ⟨k, z, v, hk, hs, hh, hf⟩ := luders_decomposition ρ hρ e he
  have hd := fun i => dephasing_bound (ρ 0 1) (z i) (v i) (ρ 0 0 - ρ 1 1).re
  sorry

private theorem measurement_attainment {n : ℕ} (hn : 2 ≤ n)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ, IsPOVM e ∧
      l1Coherence (luders e ρ) = (l1Coherence ρ + blochNorm ρ) / 2 := by
  sorry

private theorem zero_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1 := by
  sorry

private theorem maximal_gain (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ ≤ 1 / 2 ∧
      ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
        ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1]) := by
  sorry

/-- The attained maximum over all finite qubit POVMs, with both extremal gain criteria. -/
theorem result (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ)
    (n : ℕ) (hn : 2 ≤ n) :
    IsGreatest {c | ∃ e : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      IsPOVM e ∧ c = l1Coherence (luders e ρ)} ((l1Coherence ρ + blochNorm ρ) / 2) ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 0 ↔ ρ 0 0 = ρ 1 1) ∧
    (l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ ≤ 1 / 2 ∧
    ((l1Coherence ρ + blochNorm ρ) / 2 - l1Coherence ρ = 1 / 2 ↔
      ρ = Matrix.diagonal ![1, 0] ∨ ρ = Matrix.diagonal ![0, 1]) := by
  obtain ⟨e, he, hv⟩ := measurement_attainment hn ρ hρ
  refine ⟨⟨⟨e, he, hv.symm⟩, ?_⟩, zero_gain ρ hρ, maximal_gain ρ hρ⟩
  rintro c ⟨f, hf, rfl⟩
  exact measurement_bound ρ hρ f hf

end D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum
