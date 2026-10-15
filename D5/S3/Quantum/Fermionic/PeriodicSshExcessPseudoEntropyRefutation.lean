/- GID: D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim; result=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result; claim=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim
   digest: The periodic same-phase SSH excess pseudo-entropy assertion has a rational counterexample. -/

import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding
import D5.S3.Quantum.Information.InputInformationBalance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 1000000

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix Polynomial
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
  (FullOperator fullC fullC_CAR fullC_mixed_anticomm_of_lt fermionWord prefixCount)
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier (numberOperator numberOperator_eq_diagonal)
open D5.S3.Quantum.FermionicCorrelationalBound.CanonicalRdmAndPadding (fullC_entries)
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
  simp_rw [← mul_assoc]

private def modes38 : Fin 6 → Fin 6 → ℝ :=
  ![![-1, 1, -1, 1, -1, 1], ![-3, 7, -5, -7, 8, 0],
    ![-13, -7, 11, -7, 2, 14], ![-3, -7, -5, 7, 8, 0],
    ![13, -7, -11, -7, -2, 14], ![1, 1, 1, 1, 1, 1]]

private def modes58 : Fin 6 → Fin 6 → ℝ :=
  ![![-1, 1, -1, 1, -1, 1], ![-5, 7, -3, -7, 8, 0],
    ![-11, -7, 13, -7, -2, 14], ![-5, -7, -3, 7, 8, 0],
    ![11, -7, -13, -7, 2, 14], ![1, 1, 1, 1, 1, 1]]

private def eig38 : Fin 6 → ℝ := ![-11/8, -7/8, -7/8, 7/8, 7/8, 11/8]
private def eig58 : Fin 6 → ℝ := ![-13/8, -7/8, -7/8, 7/8, 7/8, 13/8]
private def modeNorm : Fin 6 → ℝ := ![6, 196, 588, 196, 588, 6]

private theorem hopping38 :
    sshHopping 3 (3/8) =
      ∑ k, (eig38 k / modeNorm k) • Matrix.vecMulVec (modes38 k) (modes38 k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sshHopping, eig38, modeNorm, modes38, Matrix.vecMulVec,
      Matrix.sum_apply, Fin.sum_univ_succ] <;> ring

private theorem hopping58 :
    sshHopping 3 (5/8) =
      ∑ k, (eig58 k / modeNorm k) • Matrix.vecMulVec (modes58 k) (modes58 k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sshHopping, eig58, modeNorm, modes58, Matrix.vecMulVec,
      Matrix.sum_apply, Fin.sum_univ_succ] <;> ring

private theorem dGamma_sum_smul {K M : ℕ} (t : Fin K → ℝ)
    (A : Fin K → Matrix (Fin M) (Fin M) ℝ) :
    dGamma (∑ k, t k • A k) = ∑ k, t k • dGamma (A k) := by
  classical
  ext s u
  simp only [dGamma, Matrix.sum_apply, Matrix.smul_apply, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [smul_eq_mul]
  push_cast
  have hsum (x : Fin M) (y : Fin M) :
      (∑ c : Fin K, (t c : ℂ) * (A c y x : ℝ)) *
      ((fullC y)ᴴ * fullC x) s u =
        ∑ c : Fin K, ((t c : ℂ) * (A c y x : ℝ)) *
          ((fullC y)ᴴ * fullC x) s u := by
    rw [Finset.sum_mul]
  simp_rw [hsum]
  simp_rw [Finset.smul_sum]
  simp_rw [Complex.real_smul]
  conv_rhs => rw [Finset.sum_comm]
  have hperm (y : Fin M) :
      (∑ x : Fin K, ∑ z : Fin M,
          (t x : ℂ) * (((A x y z : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC z) s u)) =
        ∑ z : Fin M, ∑ x : Fin K,
          (t x : ℂ) * (((A x y z : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC z) s u) := by
    rw [Finset.sum_comm]
  have hrhsperm :
      (∑ y : Fin M, ∑ x : Fin K, ∑ z : Fin M,
          (t x : ℂ) * (((A x y z : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC z) s u)) =
        ∑ y : Fin M, ∑ z : Fin M, ∑ x : Fin K,
          (t x : ℂ) * (((A x y z : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC z) s u) := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hperm y
  rw [hrhsperm]
  conv_lhs => rw [Finset.sum_comm]
  have hperm2 (y : Fin M) :
      (∑ x : Fin M, ∑ c : Fin K,
          (t c : ℂ) * ((A c y x : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC x) s u) =
        ∑ c : Fin K, ∑ x : Fin M,
          (t c : ℂ) * ((A c y x : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC x) s u := by
    rw [Finset.sum_comm]
  have hleftperm :
      (∑ y : Fin M, ∑ x : Fin M, ∑ c : Fin K,
          (t c : ℂ) * ((A c y x : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC x) s u) =
        ∑ y : Fin M, ∑ c : Fin K, ∑ x : Fin M,
          (t c : ℂ) * ((A c y x : ℝ) : ℂ) *
            ((fullC y)ᴴ * fullC x) s u := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hperm2 y
  rw [hleftperm]
  simp_rw [mul_assoc]
  have hswap3 (x : Fin M) :
      (∑ c : Fin K, ∑ z : Fin M,
          (t c : ℂ) * (((A c x z : ℝ) : ℂ) *
            ((fullC x)ᴴ * fullC z) s u)) =
        ∑ z : Fin M, ∑ c : Fin K,
          (t c : ℂ) * (((A c x z : ℝ) : ℂ) *
            ((fullC x)ᴴ * fullC z) s u) := by
    rw [Finset.sum_comm]
  have hleft3 :
      (∑ x : Fin M, ∑ c : Fin K, ∑ z : Fin M,
          (t c : ℂ) * (((A c x z : ℝ) : ℂ) *
            ((fullC x)ᴴ * fullC z) s u)) =
        ∑ x : Fin M, ∑ z : Fin M, ∑ c : Fin K,
          (t c : ℂ) * (((A c x z : ℝ) : ℂ) *
            ((fullC x)ᴴ * fullC z) s u) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hswap3 x
  rw [hleft3]

private theorem fullC_sparse {M : ℕ} (j : Fin M) (f : Assignment M → ℂ) (s : Assignment M) :
    (fullC j *ᵥ f) s =
      if s j = false then (-1 : ℂ) ^ prefixCount s j * f (Function.update s j true) else 0 := by
  sorry

private def psiCode (x : Assignment 6) : Fin 64 :=
  finFunctionFinEquiv (fun j => if x j then (1 : Fin 2) else 0)

private def psi38Int : Fin 64 → ℤ := ![0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 20, 0, -20, 4, 0, 0, 0, 0, -20, 0, 21, -5, 0, 0, -5, 5, 0, -4, 0, 0, 0, 0, 0, 0, 4, 0, -5, 5, 0, 0, 5, -21, 0, 20, 0, 0, 0, 0, -4, 20, 0, -20, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0]
private def psi58Int : Fin 64 → ℤ := ![0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 6, 0, -6, 2, 0, 0, 0, 0, -6, 0, 7, -3, 0, 0, -3, 3, 0, -2, 0, 0, 0, 0, 0, 0, 2, 0, -3, 3, 0, 0, 3, -7, 0, 6, 0, 0, 0, 0, -2, 6, 0, -6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]

private def psi38 : Assignment 6 → ℂ := fun x => (psi38Int (psiCode x) : ℂ)
private def psi58 : Assignment 6 → ℂ := fun x => (psi58Int (psiCode x) : ℂ)

private def psi38Z : Assignment 6 → ℤ := fun x => psi38Int (psiCode x)
private def psi58Z : Assignment 6 → ℤ := fun x => psi58Int (psiCode x)

private def modeInt (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ) : Assignment 6 → ℤ :=
  fun x => ∑ j, l j * (if x j = false then (-1 : ℤ) ^ prefixCount x j *
    f (Function.update x j true) else 0)

private def modeCreateInt (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ) : Assignment 6 → ℤ :=
  fun x => ∑ j, l j * (if x j = true then (-1 : ℤ) ^ prefixCount x j *
    f (Function.update x j false) else 0)

private def modes38Z : Fin 6 → Fin 6 → ℤ :=
  ![![-1, 1, -1, 1, -1, 1], ![-3, 7, -5, -7, 8, 0],
    ![-13, -7, 11, -7, 2, 14], ![-3, -7, -5, 7, 8, 0],
    ![13, -7, -11, -7, -2, 14], ![1, 1, 1, 1, 1, 1]]
private def modes58Z : Fin 6 → Fin 6 → ℤ :=
  ![![-1, 1, -1, 1, -1, 1], ![-5, 7, -3, -7, 8, 0],
    ![-11, -7, 13, -7, -2, 14], ![-5, -7, -3, 7, 8, 0],
    ![11, -7, -13, -7, 2, 14], ![1, 1, 1, 1, 1, 1]]

private theorem psi38_norm : ∑ x, psi38Z x ^ 2 = 3528 := by decide
private theorem psi58_norm : ∑ x, psi58Z x ^ 2 = 392 := by decide
private theorem psi38_overlap : ∑ x, psi58Z x * psi38Z x = 1152 := by decide
private theorem psi38_three : ∀ x : Assignment 6,
    (∑ j, if x j then (1 : ℤ) else 0) * psi38Z x = 3 * psi38Z x := by decide
private theorem psi58_three : ∀ x : Assignment 6,
    (∑ j, if x j then (1 : ℤ) else 0) * psi58Z x = 3 * psi58Z x := by decide

set_option maxRecDepth 100000 in
private theorem psi38_mode_kernel :
    (∀ k : Fin 3, modeCreateInt (modes38Z ⟨k.val, by omega⟩) psi38Z = 0) ∧
    (∀ k : Fin 3, modeInt (modes38Z ⟨k.val + 3, by omega⟩) psi38Z = 0) := by
  constructor <;> intro k <;> fin_cases k <;> decide

set_option maxRecDepth 100000 in
private theorem psi58_mode_kernel :
    (∀ k : Fin 3, modeCreateInt (modes58Z ⟨k.val, by omega⟩) psi58Z = 0) ∧
    (∀ k : Fin 3, modeInt (modes58Z ⟨k.val + 3, by omega⟩) psi58Z = 0) := by
  constructor <;> intro k <;> fin_cases k <;> decide

theorem result : ¬ claim := by
  sorry

end
end D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
