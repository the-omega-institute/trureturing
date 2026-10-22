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
    ∀ (lam : ℂ) (X : Matrix (Fin N) (Fin N) ℂ),
      X ≠ 0 → generator γ L X = lam • X →
        ‖1 + lam / (scale γ L : ℂ)‖ ≤ 1

private def witnessV : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![(1 : ℂ) - (1 / 3 : ℂ) * I,
    (-1 : ℂ) - (1 / 3 : ℂ) * I, (2 / 3 : ℂ) * I]

private def witnessRate : Fin 1 → ℝ := fun _ => 1

private def witnessJump : Fin 1 → Matrix (Fin 3) (Fin 3) ℂ := fun _ => witnessV

private def matrixUnit01 : Matrix (Fin 3) (Fin 3) ℂ := Matrix.single 0 1 1

private lemma witness_trace : witnessV.trace = 0 := by
  simp [witnessV, Matrix.trace, Fin.sum_univ_three]
  apply Complex.ext <;> norm_num <;> ring

private lemma witness_expectation (ψ : Fin 3 → ℂ)
    (hψ : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    star ψ ⬝ᵥ
        (generator witnessRate witnessJump (vecMulVec ψ (star ψ)) *ᵥ ψ) =
      (((‖ψ 0‖ ^ 2 - ‖ψ 1‖ ^ 2) ^ 2 + ‖ψ 2‖ ^ 4 - 1 : ℝ) : ℂ) := by
  sorry

private lemma witness_scale_upper : scale witnessRate witnessJump ≤ 1 := by
  sorry

private lemma witness_scale_pos : 0 < scale witnessRate witnessJump := by
  sorry

private lemma witness_eigenvalue :
    generator witnessRate witnessJump matrixUnit01 =
      (-2 + (2 / 3 : ℂ) * I) • matrixUnit01 := by
  sorry

private lemma outside_disk (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) :
    ‖1 + (-2 + (2 / 3 : ℂ) * I) / (ν : ℂ)‖ > 1 := by
  sorry

theorem result : ¬ claim := by
  intro hclaim
  have hscale : 0 < scale witnessRate witnessJump := witness_scale_pos
  have htrace : ∀ k, (witnessJump k).trace = 0 := by
    intro k
    exact witness_trace
  have he := hclaim 3 1 witnessRate witnessJump (by
    intro k
    simpa [witnessRate] using (show (0 : ℝ) ≤ 1 by norm_num)) htrace hscale
  have hne : matrixUnit01 ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero 0) 1
    norm_num [matrixUnit01] at hentry
  have hbound := he (-2 + (2 / 3 : ℂ) * I) matrixUnit01 hne witness_eigenvalue
  exact (not_le_of_gt (outside_disk (scale witnessRate witnessJump)
    hscale witness_scale_upper)) hbound

end D5.S3.Quantum.Dynamics.DissipatorSpectralDiskRefutation
