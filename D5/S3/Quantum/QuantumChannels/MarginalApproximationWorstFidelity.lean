/- GID: D5/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/MarginalApproximationWorstFidelity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp worst-case fidelity of the product of process-matrix marginals. -/

import D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness
import Mathlib.Analysis.MeanInequalities
import Mathlib.Logic.Equiv.Fin.Rotate

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open D5.S3.Quantum.Information.NMLWMeasuredFidelitySeparation (uhlmann)
open D5.S3.Quantum.Foundation.FiniteTraceDistance

noncomputable section
namespace D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity

/-- A tensor product of Pauli matrices, in the order identity, X, Y, Z. -/
def pauliString {N : ℕ} (a : Fin N → Fin 4) :
    Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun x y => ∏ i, sigma (a i) (x i) (y i)

/-- Positivity and trace preservation in the unnormalized Pauli basis. -/
def IsProcessCPTP {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) : Prop :=
  χ.PosSemidef ∧ ∑ a, ∑ b, χ a b • (pauliString b * pauliString a) = 1

/-- The partial trace onto one four-dimensional site. -/
def marginal {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (k : Fin N) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => ∑ y, if y k = i then χ y (Function.update y k j) else 0

/-- The tensor product of all single-site process-matrix marginals. -/
def marginalApprox {N : ℕ} (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) :
    Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  fun a b => ∏ k, marginal χ k (a k) (b k)

/-- Squared Uhlmann root fidelity. -/
def fidelity {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  (uhlmann ρ σ) ^ 2

/-- The wire permutation with entry one exactly when `x = y ∘ finRotate N`. -/
def cyclicShift (N : ℕ) : Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ :=
  fun x y => if x = y ∘ finRotate N then 1 else 0

/-- Pauli expansion coefficients of the cyclic wire permutation. -/
def shiftCoeff (N : ℕ) (a : Fin N → Fin 4) : ℂ :=
  (2 ^ N : ℂ)⁻¹ * Matrix.trace (pauliString a * cyclicShift N)

/-- The rank-one process matrix of the cyclic wire permutation. -/
def shiftProcess (N : ℕ) : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ :=
  Matrix.vecMulVec (shiftCoeff N) (star (shiftCoeff N))

/-- The universal lower bound and its cyclic-shift attainment. -/
def claim : Prop :=
  (∀ N, 1 ≤ N → ∀ χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ,
    IsProcessCPTP χ → (1 / 4 ^ N : ℝ) ≤ fidelity χ (marginalApprox χ)) ∧
  (∀ N, 2 ≤ N →
    (∑ a, shiftCoeff N a • pauliString a = cyclicShift N) ∧
    IsProcessCPTP (shiftProcess N) ∧
    (∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1) ∧
    fidelity (shiftProcess N) (marginalApprox (shiftProcess N)) = 1 / 4 ^ N)

private lemma classical_overlap {N : ℕ} (p : (Fin N → Fin 4) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) :
    (1 / 4 ^ N : ℝ) ≤
      ∑ x, p x * ∏ k, ∑ y, if y k = x k then p y else 0 := by
  sorry

private lemma process_trace {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : IsProcessCPTP χ) :
    Matrix.trace χ = 1 := by
  sorry

private lemma marginalApprox_psd {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ) (hχ : χ.PosSemidef) :
    (marginalApprox χ).PosSemidef := by
  sorry

private lemma quantum_overlap {N : ℕ}
    (χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ)
    (hχ : χ.PosSemidef) (ht : Matrix.trace χ = 1)
    (hc : ∀ p : (Fin N → Fin 4) → ℝ, (∀ x, 0 ≤ p x) → ∑ x, p x = 1 →
      (1 / 4 ^ N : ℝ) ≤
        ∑ x, p x * ∏ k, ∑ y, if y k = x k then p y else 0) :
    (1 / 4 ^ N : ℝ) ≤ (Matrix.trace (χ * marginalApprox χ)).re := by
  sorry

private lemma fidelity_overlap {n : Type*} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) :
    (Matrix.trace (ρ * σ)).re ≤ fidelity ρ σ := by
  sorry

private lemma shift_expansion (N : ℕ) :
    ∑ a, shiftCoeff N a • pauliString a = cyclicShift N := by
  sorry

private lemma shift_unitary (N : ℕ) : (cyclicShift N)ᴴ * cyclicShift N = 1 := by
  sorry

private lemma shift_cptp (N : ℕ)
    (he : ∑ a, shiftCoeff N a • pauliString a = cyclicShift N)
    (hu : (cyclicShift N)ᴴ * cyclicShift N = 1) : IsProcessCPTP (shiftProcess N) := by
  sorry

private lemma shift_marginals (N : ℕ) (hN : 2 ≤ N) :
    ∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1 := by
  sorry

private lemma shift_fidelity (N : ℕ)
    (hχ : IsProcessCPTP (shiftProcess N))
    (hm : ∀ k, marginal (shiftProcess N) k = (1 / 4 : ℂ) • 1) :
    fidelity (shiftProcess N) (marginalApprox (shiftProcess N)) = 1 / 4 ^ N := by
  sorry

/-- Every process matrix satisfies the bound, and cyclic shifts attain it for at least two qubits. -/
theorem result : claim := by
  constructor
  · intro N _ χ hχ
    exact (quantum_overlap χ hχ.1 (process_trace χ hχ) classical_overlap).trans
      (fidelity_overlap χ (marginalApprox χ) hχ.1 (marginalApprox_psd χ hχ.1))
  · intro N hN
    have he := shift_expansion N
    have hχ := shift_cptp N he (shift_unitary N)
    have hm := shift_marginals N hN
    exact ⟨he, hχ, hm, shift_fidelity N hχ hm⟩

end D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
