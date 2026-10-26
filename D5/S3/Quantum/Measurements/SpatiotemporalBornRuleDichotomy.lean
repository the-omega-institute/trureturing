/- GID: D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A Born rule for sequential measurements forces a scalar state or replacement channel. -/

import D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section
open scoped BigOperators Kronecker
open Matrix

namespace D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy

open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation (IsCPTP)
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

/-- An orthogonal projection of arbitrary rank. -/
def IsProj {d : ℕ} (p : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  p * p = p ∧ p.IsHermitian

/-- One bipartite operator represents all pairs of sequential projective outcomes. -/
def BornRuleExists {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) : Prop :=
  ∃ w : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ,
    ∀ p q, IsProj p → IsProj q →
      (w * (p ⊗ₖ q)).trace = (ε (p * ρ * p) * q).trace

/-- A channel discards its input and prepares one fixed density matrix. -/
def DiscardPrepare {d e : ℕ} (ε : MatrixMap (Fin d) (Fin e) ℂ) : Prop :=
  ∃ σ : Matrix (Fin e) (Fin e) ℂ, IsDensity σ ∧ ∀ x, ε x = x.trace • σ

/-- The spatiotemporal Born rule dichotomy in all positive finite dimensions. -/
def claim : Prop :=
  ∀ (d e : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ),
    IsDensity ρ → IsCPTP ε → 1 ≤ d → 1 ≤ e →
    (BornRuleExists ρ ε ↔ ρ = (1 / (d : ℂ)) • 1 ∨ DiscardPrepare ε)

private lemma born_identity {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (h : BornRuleExists ρ ε) :
    ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p) := by
  sorry

private lemma eigenbasis_assembly {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (hρ : IsDensity ρ) (hε : IsCPTP ε)
    (hd : 1 ≤ d)
    (hid : ∀ p, IsProj p → ε (p * ρ + ρ * p) = (2 : ℂ) • ε (p * ρ * p)) :
    ρ = (1 / (d : ℂ)) • 1 ∨ DiscardPrepare ε := by
  sorry

private lemma born_of_discard {d e : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ)
    (ε : MatrixMap (Fin d) (Fin e) ℂ) (h : DiscardPrepare ε) :
    BornRuleExists ρ ε := by
  sorry

private lemma born_of_scalar {d e : ℕ} (ε : MatrixMap (Fin d) (Fin e) ℂ) :
    BornRuleExists ((1 / (d : ℂ)) • 1) ε := by
  sorry

/-- A universal LvN Born rule exists exactly in the two stated cases. -/
theorem result : claim := by
  intro d e ρ ε hρ hε hd _he
  constructor
  · intro h
    exact eigenbasis_assembly ρ ε hρ hε hd (born_identity ρ ε h)
  · rintro (rfl | h)
    · exact born_of_scalar ε
    · exact born_of_discard ρ ε h

end D5.S3.Quantum.Measurements.SpatiotemporalBornRuleDichotomy
