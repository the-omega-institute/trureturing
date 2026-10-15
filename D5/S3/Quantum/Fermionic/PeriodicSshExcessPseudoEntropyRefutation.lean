/- GID: D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim; result=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result; claim=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim
   digest: The periodic same-phase SSH excess pseudo-entropy assertion has a rational counterexample. -/

import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.Information.InputInformationBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix Polynomial
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner (FullOperator fullC)
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier (numberOperator numberOperator_eq_diagonal)
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

namespace D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation

noncomputable section

def sshHopping (N : ℕ) (v : ℝ) : Matrix (Fin (2*N)) (Fin (2*N)) ℝ :=
  fun i j =>
    (if i.val / 2 = j.val / 2 ∧ i ≠ j then v else 0) +
    (if (i.val % 2 = 1 ∧ j.val = (i.val + 1) % (2*N)) ∨
        (j.val % 2 = 1 ∧ i.val = (j.val + 1) % (2*N)) then 1 else 0)

def hamiltonian (N : ℕ) (v : ℝ) : FullOperator (2*N) :=
  ∑ i, ∑ j, ((sshHopping N v i j : ℝ) : ℂ) • ((fullC i)ᴴ * fullC j)

def IsHalfFilledGroundState (N : ℕ) (v : ℝ) (ψ : Assignment (2*N) → ℂ) : Prop :=
  ψ ≠ 0 ∧ numberOperator (2*N) *ᵥ ψ = (N : ℂ) • ψ ∧
  ∀ φ : Assignment (2*N) → ℂ, φ ≠ 0 → numberOperator (2*N) *ᵥ φ = (N : ℂ) • φ →
    (star ψ ⬝ᵥ (hamiltonian N v *ᵥ ψ)).re * (star φ ⬝ᵥ φ).re ≤
      (star φ ⬝ᵥ (hamiltonian N v *ᵥ φ)).re * (star ψ ⬝ᵥ ψ).re

def reduce {N L : ℕ} (h : 2*L ≤ 2*N) (X : FullOperator (2*N)) : FullOperator (2*L) :=
  fun a b => ∑ x, ∑ y,
    if (∀ i : Fin (2*L), x (Fin.castLE h i) = a i) ∧ (∀ i : Fin (2*L), y (Fin.castLE h i) = b i) ∧
       (∀ k : Fin (2*N), 2*L ≤ k.val → x k = y k) then X x y else 0

def matrixEntropy {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) : ℂ :=
  (X.charpoly.roots.map (fun z => -(z * Complex.log z))).sum

def averagedExcess {N L : ℕ} (h : 2*L ≤ 2*N) (ψ₁ ψ₂ : Assignment (2*N) → ℂ) : ℝ :=
  (matrixEntropy (reduce h ((star ψ₂ ⬝ᵥ ψ₁)⁻¹ • Matrix.vecMulVec ψ₁ (star ψ₂)))).re -
  ((matrixEntropy (reduce h ((star ψ₁ ⬝ᵥ ψ₁)⁻¹ • Matrix.vecMulVec ψ₁ (star ψ₁)))).re +
   (matrixEntropy (reduce h ((star ψ₂ ⬝ᵥ ψ₂)⁻¹ • Matrix.vecMulVec ψ₂ (star ψ₂)))).re) / 2

def claim : Prop :=
  ∀ (N L : ℕ) (h : 2*L ≤ 2*N), 1 ≤ L → L < N → ∀ v₁ v₂ : ℝ,
    ((|v₁| < 1 ∧ |v₂| < 1) ∨ (1 < |v₁| ∧ 1 < |v₂|)) →
    ∀ ψ₁ ψ₂ : Assignment (2*N) → ℂ,
      IsHalfFilledGroundState N v₁ ψ₁ → IsHalfFilledGroundState N v₂ ψ₂ → star ψ₂ ⬝ᵥ ψ₁ ≠ 0 →
      averagedExcess h ψ₁ ψ₂ ≤ 0

end
end D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
