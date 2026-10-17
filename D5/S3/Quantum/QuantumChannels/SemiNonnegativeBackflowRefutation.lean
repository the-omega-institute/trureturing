/- GID: D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim; result=D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.result; claim=D5/S3/Quantum/QuantumChannels/SemiNonnegativeBackflowRefutation.claim
   digest: A non-SP semi-nonnegative qutrit map doubles trace distance in a Kraus context. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoTraceNormCMIRefutation
import D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap (of_kraus)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)

namespace D5.S3.Quantum.QuantumChannels.SemiNonnegativeBackflowRefutation

/-- Hermiticity and trace preservation for a complex-linear matrix map. -/
def IsHPTP {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ X, Ψ Xᴴ = (Ψ X)ᴴ) ∧ ∀ X, trace (Ψ X) = trace X

/-- Some positive-definite density has a positive-definite density image. -/
def IsSemiPositive {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ ρ, IsDensity ρ ∧ ρ.PosDef ∧ IsDensity (Ψ ρ) ∧ (Ψ ρ).PosDef

/-- Some density has a density image. -/
def IsSemiNonnegative {d : ℕ} (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
    Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ ρ, IsDensity ρ ∧ IsDensity (Ψ ρ)

/-- The existing finite Kraus linear map, evaluated on a matrix. -/
def krausApply {d : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :=
  of_kraus K K X

/-- Normalization of a finite Kraus family. -/
def IsKrausChannel {d : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin d) (Fin d) ℂ) : Prop := ∑ r, (K r)ᴴ * K r = 1

/-- The matrix trace distance, using the canonical trace norm. -/
def traceDistance {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- The no-backflow conjunct of the higher-dimensional non-SP SNTP conjecture. -/
def claim : Prop :=
  ∀ (d : ℕ) (Ψ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ),
    IsHPTP Ψ ∧ IsSemiNonnegative Ψ ∧ ¬ IsSemiPositive Ψ →
    ∀ (ι κ : Type) [Fintype ι] [Fintype κ]
      (K : ι → Matrix (Fin d) (Fin d) ℂ) (L : κ → Matrix (Fin d) (Fin d) ℂ),
      IsKrausChannel K → IsKrausChannel L →
      (∀ X, Ψ (krausApply K X) = krausApply L X) →
      ∀ σ₁ σ₂, IsDensity σ₁ → IsDensity σ₂ →
        traceDistance (krausApply L σ₁) (krausApply L σ₂) ≤
          traceDistance (krausApply K σ₁) (krausApply K σ₂)

private def psi : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ where
  toFun X :=
    !![2 * X 0 0 - (X 0 0 + X 1 1) / 2 + X 2 2, 2 * X 0 1, X 0 2;
       2 * X 1 0, 2 * X 1 1 - (X 0 0 + X 1 1) / 2 + X 2 2, X 1 2;
       X 2 0, X 2 1, -X 2 2]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring

end D5.S3.Quantum.QuantumChannels.SemiNonnegativeBackflowRefutation
