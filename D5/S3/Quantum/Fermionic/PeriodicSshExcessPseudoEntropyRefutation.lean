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
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
  (FullOperator fullC fullC_CAR fullC_mixed_anticomm_of_lt)
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

private def mode {M : ℕ} (l : Fin M → ℝ) : FullOperator M :=
  ∑ j, (l j : ℂ) • fullC j

private def dGamma {M : ℕ} (h : Matrix (Fin M) (Fin M) ℝ) : FullOperator M :=
  ∑ i, ∑ j, (h i j : ℂ) • ((fullC i)ᴴ * fullC j)

private theorem fullC_mixed (M : ℕ) (i j : Fin M) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i =
      if i = j then (1 : FullOperator M) else 0 := by
  by_cases hij : i = j
  · subst j; simp [fullC_CAR]
  · rcases lt_or_gt_of_ne hij with h | h
    · exact (fullC_mixed_anticomm_of_lt i j h).trans (by simp [hij])
    · have ht := congrArg Matrix.conjTranspose (fullC_mixed_anticomm_of_lt j i h)
      simpa [hij] using ht

private theorem mode_car {M : ℕ} (l : Fin M → ℝ) :
    mode l * (mode l)ᴴ + (mode l)ᴴ * mode l =
      ((∑ j, l j ^ 2 : ℝ) : ℂ) • (1 : FullOperator M) := by
  classical
  unfold mode
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, smul_add, add_smul, Finset.smul_sum]
  have hswap :
      (∑ i, ∑ j, (l i : ℂ) • (l j : ℂ) • (fullC j * (fullC i)ᴴ)) =
        ∑ i, ∑ j, (l i : ℂ) • (l j : ℂ) • (fullC i * (fullC j)ᴴ) := by
    rw [Finset.sum_comm]
    simp_rw [smul_smul]
    simp [mul_comm]
  rw [hswap]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  simp_rw [← smul_add]
  have hcar (i j : Fin M) :
      fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i =
        if i = j then (1 : FullOperator M) else 0 := fullC_mixed M i j
  have hrhs : ((∑ j, l j ^ 2 : ℝ) : ℂ) • (1 : FullOperator M) =
      ∑ j, ((l j : ℂ) ^ 2) • (1 : FullOperator M) := by
    simpa [map_sum] using
      (Finset.sum_smul (R := ℂ) (M := FullOperator M)
        (s := Finset.univ) (f := fun j : Fin M => (l j : ℂ) ^ 2)
        (x := (1 : FullOperator M)))
  rw [Finset.sum_comm]
  simp_rw [smul_smul]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i hi
  have hrhs_i : ((l i : ℂ) ^ 2) • (1 : FullOperator M) =
      ∑ j, ((l j : ℂ) * (l i : ℂ)) •
        (if j = i then (1 : FullOperator M) else 0) := by
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm, pow_two]
  rw [hrhs_i]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcar j i]

private theorem dGamma_rankOne {M : ℕ} (l : Fin M → ℝ) :
    dGamma (Matrix.vecMulVec l l) = (mode l)ᴴ * mode l := by
  classical
  unfold dGamma mode Matrix.vecMulVec
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  simp [Matrix.vecMulVec, Matrix.of_apply, smul_smul, Algebra.smul_def,
    Complex.ofReal_mul, mul_comm]
  noncomm_ring

end
end D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
