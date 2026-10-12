/- GID: D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim; result=D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.result; claim=D5/S3/Quantum/Measurement/KvashchukMulticopyDesignRefutation.claim
   digest: Weighted multicopy designs and qubit discrimination beyond the design construction. -/

import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation
import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.Tactic.FinCases

set_option linter.style.longLine false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (IsPure)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)
open D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation (success)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

namespace D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation

def tensorPow {d : ℕ} (k : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  fun i j => ∏ t : Fin k, A (finFunctionFinEquiv.symm i t) (finFunctionFinEquiv.symm j t)

def permOp (d k : ℕ) (σ : Equiv.Perm (Fin k)) :
    Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ := by
  classical
  exact fun i j => if finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j ∘ σ then 1 else 0

def PiSym (d k : ℕ) : Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ :=
  (k.factorial : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), permOp d k σ

def IsWeightedDesign {d N : ℕ} (k : ℕ) (ρ : Fin N → DensityState (Fin d))
    (p : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ (∀ i, 0 < p i → IsPure (ρ i)) ∧
    ∑ i, (p i : ℂ) • tensorPow k (ρ i).1 = (trace (PiSym d k))⁻¹ • PiSym d k

def DesignExists (d k N : ℕ) : Prop :=
  ∃ ρ : Fin N → DensityState (Fin d), ∃ p : Fin N → ℝ, IsWeightedDesign k ρ p

def Nprime (d k : ℕ) : ℕ := sInf {N : ℕ | DesignExists d k N}

def maxMixed (d : ℕ) (hd : 0 < d) : DensityState (Fin d) := by
  refine ⟨CStarMatrix.ofMatrix ((d : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg d))).nonneg)
  · change trace ((d : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℂ)) = 1
    simp [trace_smul, hd.ne', Complex.real_smul]

def adjoin {d N : ℕ} (ρ : Fin N → DensityState (Fin d)) (hd : 0 < d) :
    Fin (N + 1) → DensityState (Fin d) :=
  Fin.lastCases (maxMixed d hd) ρ

def Discr {d N : ℕ} (k : ℕ) (ρ : Fin N → DensityState (Fin d)) : ℝ :=
  sSup {r : ℝ | ∃ E : Fin N → Matrix (Fin (d ^ k)) (Fin (d ^ k)) ℂ,
    IsPOVM E ∧ r = success (fun i => tensorPow k (ρ i).1) E}

def claim : Prop :=
  ∀ d k : ℕ, ∀ hd : 0 < d, 0 < k →
    ∀ (ρ : Fin (Nprime d k) → DensityState (Fin d)) (p : Fin (Nprime d k) → ℝ),
      IsWeightedDesign k ρ p → ∀ E : Fin (Nprime d k + 1) → DensityState (Fin d),
        Discr k E ≤ Discr k (adjoin ρ hd)

end D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation
