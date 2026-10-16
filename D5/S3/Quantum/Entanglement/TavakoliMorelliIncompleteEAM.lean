/- GID: D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/TavakoliMorelliIncompleteEAM
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Incomplete equiangular measurements and Schmidt-number correlation bounds. -/

import D5.S3.Quantum.Foundation.FiniteDensityPurification
import D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability
import D5.S3.Quantum.Analysis.TraceClass.IdealNorm
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Vec

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteTraceDistance

namespace D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM

abbrev Op (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev BipartiteOp (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
abbrev proj {ι : Type*} [Fintype ι] [DecidableEq ι] (u : Ket ι) : Matrix ι ι ℂ :=
  (MState.pure u).m

def coeff {d : ℕ} (u : Ket (Fin d × Fin d)) : Op d :=
  Matrix.of fun i j => u.vec (i, j)

def SchmidtNumberLE {d : ℕ} (ρ : BipartiteOp d) (r : ℕ) : Prop :=
  ∃ (N : ℕ) (p : Fin N → ℝ) (u : Fin N → Ket (Fin d × Fin d)),
    (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
    (∀ k, (coeff (u k)).rank ≤ r) ∧ ρ = ∑ k, (p k : ℂ) • proj (u k)

def correlation {d : ℕ} {κ : Type*} [Fintype κ]
    (ρ : BipartiteOp d) (A B : κ → Op d) : Matrix κ κ ℂ :=
  Matrix.of fun a b => (((ρ * Matrix.kronecker (A a) (B b)).trace).re : ℂ)

def hsSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def moment {d : ℕ} {κ : Type*} [Fintype κ] (A : κ → Op d) (H : Op d) : ℝ :=
  ∑ a, ((H * A a).trace.re) ^ 2

def ScaledPure {d : ℕ} (A : Op d) : Prop :=
  ∃ (c : ℝ) (u : Ket (Fin d)), 0 ≤ c ∧ A = (c : ℂ) • proj u

def MomentBound {d : ℕ} {κ : Type*} [Fintype κ]
    (A : κ → Op d) (α β : ℝ) : Prop :=
  ∀ H : Op d, H.IsHermitian →
    moment A H ≤ α * (H * H).trace.re + β * (H.trace.re) ^ 2

def EAM (d n : ℕ) :=
  {ket : Fin n → Ket (Fin d) // d < n ∧
    (∑ a, proj (ket a)) = ((n : ℂ) / (d : ℂ)) • (1 : Op d) ∧
    ∀ a b, a ≠ b → ‖dotProduct (star (ket a).vec) (ket b).vec‖ ^ 2 =
      ((n : ℝ) - (d : ℝ)) / ((d : ℝ) * ((n : ℝ) - 1))}

def EAM.effect {d n : ℕ} (A : EAM d n) (a : Fin n) : Op d :=
  ((d : ℂ) / (n : ℂ)) • proj (A.val a)

def Pn {d n : ℕ} (ρ : BipartiteOp d) (A B : EAM d n) : Matrix (Fin n) (Fin n) ℂ :=
  correlation ρ A.effect B.effect

def claim : Prop :=
  ∀ (d n r : ℕ), 1 ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : EAM d n) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (Pn ρ A B) ≤
        ((d : ℝ) * ((d : ℝ) - 1) + (r : ℝ) * ((n : ℝ) - (d : ℝ))) /
          ((n : ℝ) * ((n : ℝ) - 1))

end D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
