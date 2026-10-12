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

-- In the ordered three-qubit basis, the rightmost tensor factor is the low bit.
private def bit (i : Fin 8) (t : Fin 3) : Fin 2 := finFunctionFinEquiv.symm i t

private theorem tensor23 (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 8) :
    tensorPow 3 A i j = A (bit i 2) (bit j 2) * A (bit i 1) (bit j 1) *
      A (bit i 0) (bit j 0) := by
  simp only [tensorPow, bit, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Fin.succ_zero_eq_one, Fin.reduceSucc]
  ring

private def weight : Fin 8 → ℕ := ![0,1,1,2,1,2,2,3]

private def P8 : Matrix (Fin 8) (Fin 8) ℂ :=
  fun i j => if weight i = weight j then
    if weight i = 0 ∨ weight i = 3 then 1 else 1 / 3 else 0

set_option maxHeartbeats 4000000 in
-- Kernel reduction enumerates all permutations of the three-element type.
private theorem perms3 : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
    {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
      Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1} := by
  decide

private theorem bit_table (i : Fin 8) (t : Fin 3) : bit i t =
    (![![0,0,0],![1,0,0],![0,1,0],![1,1,0],![0,0,1],![1,0,1],![0,1,1],![1,1,1]] :
      Fin 8 → Fin 3 → Fin 2) i t := by
  fin_cases i <;> fin_cases t <;> rfl

private theorem permOp23 (σ : Equiv.Perm (Fin 3)) (i j : Fin 8) :
    permOp 2 3 σ i j = if (fun t => bit i t) = (fun t => bit j (σ t)) then 1 else 0 := rfl

private theorem sum_perms3 (f : Equiv.Perm (Fin 3) → ℂ) :
    ∑ σ, f σ = f 1 + f (Equiv.swap 0 1) + f (Equiv.swap 0 2) +
      f (Equiv.swap 1 2) + f (Equiv.swap 0 1 * Equiv.swap 1 2) +
      f (Equiv.swap 1 2 * Equiv.swap 0 1) := by
  rw [perms3]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  ring

set_option maxHeartbeats 2000000 in
-- The symmetriser certificate checks all 64 entries.
private theorem piSym23 : PiSym 2 3 = P8 := by
  classical
  unfold PiSym
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  rw [sum_perms3]
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hb : (0 : Fin 2) ≠ 1 := by decide
  fin_cases i <;> fin_cases j <;>
    norm_num [permOp23, bit_table, P8, weight, Matrix.smul_apply, Matrix.sum_apply,
      Function.comp_def, Matrix.cons_val_two,
      funext_iff, Fin.forall_fin_succ, Equiv.swap_apply_def, Equiv.Perm.mul_apply, Fin.reduceSucc,
      h01, h02, h12, hb, Ne.symm h01, Ne.symm h02, Ne.symm h12, Ne.symm hb]

private theorem trace_P8 : trace P8 = 4 := by
  norm_num [trace, P8, weight, Fin.sum_univ_succ]

end D5.S3.Quantum.Measurement.KvashchukMulticopyDesignRefutation
