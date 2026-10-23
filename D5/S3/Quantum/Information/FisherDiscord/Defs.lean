/- GID: D5/S3/Quantum/Information/FisherDiscord/Defs
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FisherDiscord/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order, mathlib/module/Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Kronecker]
   utility: none
   digest: Density matrices, symmetric logarithmic derivatives and partial trace for Fisher discord. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Information.FisherDiscord.Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive semidefinite matrix of unit trace. -/
def IsDensity (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- Trace over the second tensor factor, in product coordinates. -/
def partialTrace₂ {d₁ d₂ : ℕ}
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ) :
    Matrix (Fin d₁) (Fin d₁) ℂ := fun i j => ∑ b, ρ (i, b) (j, b)

/-- The local observable tensored with the identity. -/
def liftLeft {d₁ d₂ : ℕ} (H : Matrix (Fin d₁) (Fin d₁) ℂ) :
    Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ :=
  Matrix.kroneckerMap (· * ·) H (1 : Matrix (Fin d₂) (Fin d₂) ℂ)

/-- A Hermitian symmetric logarithmic derivative for the unitary tangent. -/
def IsSLD (ρ H L : Matrix n n ℂ) : Prop :=
  L.IsHermitian ∧ Complex.I • (ρ * H - H * ρ) = (1 / 2 : ℂ) • (L * ρ + ρ * L)

/-- The Fisher information in the source normalization. -/
def fisherSLD (ρ L : Matrix n n ℂ) : ℝ := (1 / 4) * (Matrix.trace (ρ * L * L)).re

/-- Wigner--Yanase skew information, using the positive matrix square root. -/
def skewWY (ρ H : Matrix n n ℂ) : ℝ :=
  -(1 / 2) * (Matrix.trace ((CFC.sqrt ρ * H - H * CFC.sqrt ρ) ^ 2)).re

/-- Partial trace does not increase Fisher discord.
The source defines Fisher information through any Hermitian SLD solution.
Its value is independent of that solution, as established by the spectral formula;
the universal quantifiers over SLD solutions express precisely this convention. -/
def claim : Prop :=
  ∀ (d₁ d₂ : ℕ)
    (ρ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ)
    (H : Matrix (Fin d₁) (Fin d₁) ℂ)
    (L₁₂ : Matrix (Fin d₁ × Fin d₂) (Fin d₁ × Fin d₂) ℂ)
    (L₁ : Matrix (Fin d₁) (Fin d₁) ℂ),
    IsDensity ρ → H.IsHermitian → IsSLD ρ (liftLeft (d₂ := d₂) H) L₁₂ →
    IsSLD (partialTrace₂ ρ) H L₁ →
    fisherSLD (partialTrace₂ ρ) L₁ - skewWY (partialTrace₂ ρ) H ≤
      fisherSLD ρ L₁₂ - skewWY ρ (liftLeft (d₂ := d₂) H)

end D5.S3.Quantum.Information.FisherDiscord.Defs
