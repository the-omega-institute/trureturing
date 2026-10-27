/- GID: D5/S3/QuantumChannels/DequantumnessPowerStrictGap
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/DequantumnessPowerStrictGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim; result=D5/S3/QuantumChannels/DequantumnessPowerStrictGap.result; claim=D5/S3/QuantumChannels/DequantumnessPowerStrictGap.claim
   digest: A translated qubit contraction has strictly greater unrestricted dequantumness power. -/

import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation
import D5.S3.Quantum.Information.ActualPureQubitGeometry
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity IsCPTP)
open D5.S3.Quantum.Information.ActualPureQubitGeometry

noncomputable section
namespace D5.S3.QuantumChannels.DequantumnessPowerStrictGap

/-- Equation (1) for the two weights `p` and `1-p`. -/
def quantumness (p : ℝ) (ρ σ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  -(∑ i : Fin 2, ∑ j : Fin 2,
    (![p, 1-p] i * ![p, 1-p] j) *
      (Matrix.trace ((![ρ, σ] i * ![ρ, σ] j - ![ρ, σ] j * ![ρ, σ] i)^2)).re)

/-- All two-state qubit ensembles, including zero weights. -/
def TwoStateEnsemble (p : ℝ) (ρ σ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ IsDensity ρ ∧ IsDensity σ

/-- The source's unrestricted two-ingredient dequantumness power. -/
def dequantumnessPower (λ : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧
    x = quantumness p ρ σ - quantumness p (λ ρ) (λ σ)}

/-- The supremum of Equation (1) over all two-state qubit ensembles. -/
def maxQuantumness : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ x = quantumness p ρ σ}

/-- The source's restriction to ensembles attaining maximal initial quantumness. -/
def restrictedDequantumnessPower (λ : MatrixMap (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {x | ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧ quantumness p ρ σ = maxQuantumness ∧
    x = quantumness p ρ σ - quantumness p (λ ρ) (λ σ)}

/-- Universal equality of the two source notions for qubit channels. -/
def claim : Prop := ∀ λ : MatrixMap (Fin 2) (Fin 2) ℂ,
  IsCPTP λ → dequantumnessPower λ = restrictedDequantumnessPower λ

private def channel : MatrixMap (Fin 2) (Fin 2) ℂ where
  toFun x := (1/2 : ℂ) • x + (Matrix.trace x / 2) • !![(3/4 : ℂ), 0; 0, 1/4]
  map_add' x y := by simp only [Matrix.trace_add, add_div, add_smul, smul_add]; abel
  map_smul' c x := by
    simp only [Matrix.trace_smul, smul_add, smul_smul, RingHom.id_apply]
    congr 1 <;> congr 1 <;> ring

private lemma orthonormal_cross_lower (r s : Fin 3 → ℝ)
    (hr : r ⬝ᵥ r = 1) (hs : s ⬝ᵥ s = 1) (hrs : r ⬝ᵥ s = 0) :
    let f := fun x : Fin 3 → ℝ => (1/2 : ℝ) • x + (1/4 : ℝ) • ![0, 0, 1]
    (1/4 : ℝ) * (1/2 - Real.sqrt 2 / 4)^2 ≤ (f r ⨯₃ f s) ⬝ᵥ (f r ⨯₃ f s) := by
  sorry

private lemma density_bloch (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : IsDensity ρ) :
    ∃ r : EuclideanSpace ℝ (Fin 3), ρ = blochMatrix 1 r ∧ r.ofLp ⬝ᵥ r.ofLp ≤ 1 := by
  sorry

private lemma quantumness_bloch (p : ℝ) (r s : EuclideanSpace ℝ (Fin 3)) :
    quantumness p (blochMatrix 1 r) (blochMatrix 1 s) =
      p * (1-p) * ((r.ofLp ⨯₃ s.ofLp) ⬝ᵥ (r.ofLp ⨯₃ s.ofLp)) := by
  sorry

private lemma quantumness_bounds {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) : 0 ≤ quantumness p ρ σ ∧ quantumness p ρ σ ≤ 1/4 := by
  sorry

private lemma max_quantumness : maxQuantumness = 1/4 := by
  sorry

private lemma maximal_bloch {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) (hq : quantumness p ρ σ = maxQuantumness) :
    ∃ r s : EuclideanSpace ℝ (Fin 3), ρ = blochMatrix 1 r ∧ σ = blochMatrix 1 s ∧
      p = 1/2 ∧ r.ofLp ⬝ᵥ r.ofLp = 1 ∧ s.ofLp ⬝ᵥ s.ofLp = 1 ∧
      r.ofLp ⬝ᵥ s.ofLp = 0 := by
  sorry

private lemma channel_bloch (r : EuclideanSpace ℝ (Fin 3)) :
    channel (blochMatrix 1 r) =
      blochMatrix 1 (WithLp.toLp 2 ((1/2 : ℝ) • r.ofLp + (1/4 : ℝ) • ![0, 0, 1])) := by
  sorry

private lemma channel_cptp : IsCPTP channel := by
  sorry

private lemma witness_loss :
    ∃ p ρ σ, TwoStateEnsemble p ρ σ ∧
      quantumness p ρ σ - quantumness p (channel ρ) (channel σ) = 1329215/5345344 := by
  sorry

private lemma restricted_loss {p : ℝ} {ρ σ : Matrix (Fin 2) (Fin 2) ℂ}
    (h : TwoStateEnsemble p ρ σ) (hq : quantumness p ρ σ = maxQuantumness) :
    quantumness p ρ σ - quantumness p (channel ρ) (channel σ) ≤
      (29 + 2 * Real.sqrt 2) / 128 := by
  sorry

private lemma power_lower : (1329215/5345344 : ℝ) ≤ dequantumnessPower channel := by
  sorry

private lemma restricted_power_upper :
    restrictedDequantumnessPower channel ≤ (29 + 2 * Real.sqrt 2) / 128 := by
  sorry

private lemma strict_comparison :
    (29 + 2 * Real.sqrt 2) / 128 < (1329215/5345344 : ℝ) := by
  sorry

/-- The source's universal equality fails for a CPTP qubit map. -/
theorem result : ¬ claim := by
  intro h
  have he := h channel channel_cptp
  have hl := power_lower
  have hu := restricted_power_upper
  have hg := strict_comparison
  rw [he] at hl
  linarith

end D5.S3.QuantumChannels.DequantumnessPowerStrictGap
