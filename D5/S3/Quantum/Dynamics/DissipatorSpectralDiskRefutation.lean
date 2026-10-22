/- GID: D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.claim; result=D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.result; claim=D5/S3/Quantum/Dynamics/DissipatorSpectralDiskRefutation.claim
   digest: The intrinsic scale does not confine dissipative GKLS spectra to the unit disk. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Matrix.Spectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Matrix

namespace D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation

def dissipator {N : ℕ} (L ρ : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  L * ρ * Lᴴ - (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

def generator {N m : ℕ} (γ : Fin m → ℝ)
    (L : Fin m → Matrix (Fin N) (Fin N) ℂ)
    (ρ : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ k, (γ k : ℂ) • dissipator (L k) ρ

def scale {N m : ℕ} (γ : Fin m → ℝ)
    (L : Fin m → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ψ : Fin N → ℂ,
    (∑ i, ‖ψ i‖ ^ 2) = 1 ∧
      r = ‖star ψ ⬝ᵥ (generator γ L (vecMulVec ψ (star ψ)) *ᵥ ψ)‖}

def claim : Prop :=
  ∀ (N m : ℕ) (γ : Fin m → ℝ)
    (L : Fin m → Matrix (Fin N) (Fin N) ℂ),
    (∀ k, 0 ≤ γ k) → (∀ k, (L k).trace = 0) → 0 < scale γ L →
    ∀ (λ : ℂ) (X : Matrix (Fin N) (Fin N) ℂ),
      X ≠ 0 → generator γ L X = λ • X →
        ‖1 + λ / (scale γ L : ℂ)‖ ≤ 1

theorem result : ¬ claim := by
  sorry

end D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation
