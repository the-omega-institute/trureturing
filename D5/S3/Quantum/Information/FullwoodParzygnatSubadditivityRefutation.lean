/- GID: D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim; result=D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.result; claim=D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation.claim
   digest: The Werner–Holevo channel on the maximally mixed five-level state violates PDM subadditivity. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap

noncomputable section
namespace D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation

/-- Input-first Jamiołkowski matrix, with reversed matrix units in the channel argument. -/
def jamio {n m : ℕ}
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  ∑ i, ∑ j, single i j 1 ⊗ₖ E (single j i 1)

/-- The two-time pseudo-density matrix is half the indicated anticommutator. -/
def pdm {n m : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ)
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  (1 / 2 : ℝ) • ((ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) * jamio E +
    jamio E * (ρ ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)))

/-- Signed spectral entropy, defined by real functional calculus without a proof argument.
For Hermitian X this is the sum of -λ log |λ|, including the value zero at λ = 0. -/
def S {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) : ℝ :=
  (trace (cfc (fun x : ℝ => -x * Real.log |x|) X)).re

/-- Subadditivity for every finite-dimensional density and complete finite Kraus family. -/
def claim : Prop :=
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
  ∀ (ρ : Matrix (Fin n) (Fin n) ℂ), ρ.PosSemidef → trace ρ = 1 →
  ∀ (ι : Type) [Fintype ι] (K : ι → Matrix (Fin m) (Fin n) ℂ),
    (∑ k, (K k)ᴴ * K k) = 1 →
    S (pdm ρ (of_kraus K K)) ≤ S ρ + S ((of_kraus K K) ρ)

private def pairs : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

private def K (k : Fin 10) : Matrix (Fin 5) (Fin 5) ℂ :=
  (1 / 2 : ℂ) • (single (pairs k).1 (pairs k).2 1 - single (pairs k).2 (pairs k).1 1)

private def ρ : Matrix (Fin 5) (Fin 5) ℂ := (1 / 5 : ℝ) • 1

private def Ω (p : Fin 5 × Fin 5) : ℂ := if p.1 = p.2 then 1 else 0

private def P : Matrix (Fin 5 × Fin 5) (Fin 5 × Fin 5) ℂ :=
  (1 / 5 : ℝ) • vecMulVec Ω (star Ω)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem complete : (∑ k, (K k)ᴴ * K k) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [K, pairs, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.single, Complex.star_def]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem action (X : Matrix (Fin 5) (Fin 5) ℂ) :
    (of_kraus K K) X = (1 / 4 : ℂ) • (trace X • 1 - Xᵀ) := by
  change (∑ k, K k * X * (K k)ᴴ) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, pairs, Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Matrix.single, Complex.star_def, Matrix.trace] <;> ring

private theorem jamio_apply {n m : ℕ}
    (E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ)
    (a c : Fin n) (b d : Fin m) :
    jamio E (a,b) (c,d) = E (single c a 1) b d := by
  simp [jamio, Matrix.sum_apply, Matrix.kroneckerMap_apply, Matrix.single, ite_and]

end D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
