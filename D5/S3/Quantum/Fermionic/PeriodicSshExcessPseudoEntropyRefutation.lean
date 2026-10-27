/- GID: D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim; result=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.result; claim=D5/S3/Quantum/Fermionic/PeriodicSshExcessPseudoEntropyRefutation.claim
   digest: Periodic same-phase SSH ground states can have positive excess pseudo-entropy. -/

import D5.S3.Quantum.Fermionic.FockMajoranaCarrier
import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 1000000

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix Polynomial
open PredictiveThermodynamic.Physical (Assignment)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
  (FullOperator fullC prefixCount)
open D5.S3.Quantum.Fermionic.FockMajoranaCarrier
  (majorana majorana_clifford_and_parity numberOperator numberOperator_eq_diagonal)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)
open D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant (occupationCount)

namespace D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation

noncomputable section

set_option linter.style.whitespace false

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

/-- Spectral entropy, summed over the characteristic roots with algebraic multiplicity, with the
principal scalar logarithm and 0 log 0 = 0; it agrees with −Tr(X log X) wherever that matrix
function is defined. -/
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

set_option linter.style.whitespace true

private def mode {M : ℕ} (l : Fin M → ℝ) : FullOperator M :=
  ∑ j, (l j : ℂ) • fullC j
private def dGamma {M : ℕ} (h : Matrix (Fin M) (Fin M) ℝ) : FullOperator M :=
  ∑ i, ∑ j, (h i j : ℂ) • ((fullC i)ᴴ * fullC j)
theorem fullC_mixed (M : ℕ) (i j : Fin M) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i =
      if i = j then (1 : FullOperator M) else 0 := by
  classical
  have hγ := (majorana_clifford_and_parity M).2.2.2.1
  have h00 := hγ (i, false) (j, false)
  have h01 := hγ (i, false) (j, true)
  have h10 := hγ (i, true) (j, false)
  have h11 := hγ (i, true) (j, true)
  calc
    _ = (1/4 : ℂ) •
        ((majorana i false * majorana j false + majorana j false * majorana i false) +
         (majorana i true * majorana j true + majorana j true * majorana i true) +
         Complex.I • (majorana i false * majorana j true +
           majorana j true * majorana i false) -
         Complex.I • (majorana i true * majorana j false +
           majorana j false * majorana i true)) := by
      delta majorana
      simp only [Bool.false_eq_true, if_false, if_true, add_mul, mul_add,
        sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul]
      match_scalars <;> norm_num [Complex.I_sq]
    _ = _ := by
      rw [h00, h11, h01, h10]
      by_cases hij : i = j
      · simp [hij]
        module
      · simp [hij]
private theorem mode_car {M : ℕ} (l : Fin M → ℝ) :
    mode l * (mode l)ᴴ + (mode l)ᴴ * mode l =
      ((∑ j, l j ^ 2 : ℝ) : ℂ) • (1 : FullOperator M) := by
  classical
  unfold mode
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Finset.smul_sum]
  have hswap :
      (∑ i, ∑ j, (l i : ℂ) • (l j : ℂ) • (fullC j * (fullC i)ᴴ)) =
        ∑ i, ∑ j, (l i : ℂ) • (l j : ℂ) • (fullC i * (fullC j)ᴴ) := by
    rw [Finset.sum_comm]
    simp_rw [smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm (l j : ℂ) (l i : ℂ)]
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
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, pow_two]
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
  simp only [Matrix.of_apply, Complex.ofReal_mul, Complex.coe_smul]
  ext s t
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_smul, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring
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
    norm_num [sshHopping.eq_1, eig38.eq_1, modeNorm.eq_1, modes38.eq_1, Matrix.vecMulVec,
      Matrix.sum_apply, Fin.sum_univ_succ]
private theorem hopping58 :
    sshHopping 3 (5/8) =
      ∑ k, (eig58 k / modeNorm k) • Matrix.vecMulVec (modes58 k) (modes58 k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sshHopping.eq_1, eig58.eq_1, modeNorm.eq_1, modes58.eq_1, Matrix.vecMulVec,
      Matrix.sum_apply, Fin.sum_univ_succ]
private theorem dGamma_sum_smul {K M : ℕ} (t : Fin K → ℝ)
    (A : Fin K → Matrix (Fin M) (Fin M) ℝ) :
    dGamma (∑ k, t k • A k) = ∑ k, t k • dGamma (A k) := by
  classical
  ext s u
  simp only [dGamma.eq_1, Matrix.sum_apply, Matrix.smul_apply]
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
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Function.update s j true)]
  · rw [fullC_entry]
    by_cases hs : s j = false
    · rw [if_pos hs]
      have hp : prefixCount (Function.update s j true) j = prefixCount s j := by
        unfold prefixCount
        congr 1
        ext i
        by_cases hij : i < j
        · have hne : i ≠ j := ne_of_lt hij
          simp [hij, Function.update_of_ne hne]
        · simp [hij]
      have hcond : (Function.update s j true) j = true ∧
          s = Function.update (Function.update s j true) j false := by
        simp [hs]
      rw [if_pos hcond]
      simp [hp]
    · rw [if_neg hs]
      have hcond : ¬((Function.update s j true) j = true ∧
          s = Function.update (Function.update s j true) j false) := by
        intro h
        have := congrFun h.2 j
        simp [hs] at this
      rw [if_neg hcond]
      simp
  · intro b hb hne
    rw [fullC_entry]
    by_cases hs : s j = false
    · have hfalse : ¬(b j = true ∧ s = Function.update b j false) := by
        intro h
        exact hne (by
          simpa only [h.2, Function.update_idem, Function.eq_update_self_iff] using h.1)
      simp [hfalse]
    · have hfalse : s j = true := Bool.ne_false_iff.mp hs
      have hfalse' : ¬(b j = true ∧ s = Function.update b j false) := by
        intro h
        have := congrFun h.2 j
        simp [hfalse] at this
      simp [hfalse']
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))
private theorem fullC_create_sparse {M : ℕ} (j : Fin M) (f : Assignment M → ℂ)
    (s : Assignment M) :
    ((fullC j)ᴴ *ᵥ f) s =
      if s j = true then (-1 : ℂ) ^ prefixCount s j * f (Function.update s j false) else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have hentry (t : Assignment M) :
      star (fullC j t s) =
        if s j = true ∧ t = Function.update s j false
        then (-1 : ℂ) ^ prefixCount s j else 0 := by
    rw [fullC_entry]
    split_ifs <;> simp
  rw [Finset.sum_eq_single (Function.update s j false)]
  · rw [hentry]
    by_cases hs : s j = true
    · rw [if_pos hs]
      simp [hs]
    · rw [if_neg hs]
      simp [hs]
  · intro b hb hne
    rw [hentry]
    by_cases hs : s j = true
    · have hfalse : ¬(s j = true ∧ b = Function.update s j false) := by
        intro h
        exact hne h.2
      simp [hfalse]
    · have hfalse : ¬(s j = true ∧ b = Function.update s j false) := by simp [hs]
      simp [hfalse]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))
private def psiCode (x : Assignment 6) : Fin 64 :=
  finFunctionFinEquiv (fun j => finTwoEquiv.symm (x j))
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
private theorem mode_mulVec_int_cast (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ)
    (s : Assignment 6) :
    (mode (fun j => (l j : ℝ)) *ᵥ (fun x => (f x : ℂ))) s =
      (modeInt l f s : ℂ) := by
  classical
  simp only [mode.eq_1, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp only [Complex.ofReal_intCast, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    fullC_sparse]
  unfold modeInt
  push_cast
  simp
private theorem mode_create_mulVec_int_cast (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ)
    (s : Assignment 6) :
    ((mode (fun j => (l j : ℝ)))ᴴ *ᵥ (fun x => (f x : ℂ))) s =
      (modeCreateInt l f s : ℂ) := by
  classical
  simp only [mode.eq_1, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp only [Complex.ofReal_intCast, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    fullC_create_sparse]
  unfold modeCreateInt
  push_cast
  simp
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
private theorem psi38_complex_mode_kernel :
    (∀ k : Fin 3,
      (mode (fun j => (modes38Z ⟨k.val, by omega⟩ j : ℝ)))ᴴ *ᵥ psi38 = 0) ∧
    (∀ k : Fin 3,
      mode (fun j => (modes38Z ⟨k.val + 3, by omega⟩ j : ℝ)) *ᵥ psi38 = 0) := by
  constructor
  · intro k
    funext s
    change ((mode (fun j => (modes38Z ⟨k.val, by omega⟩ j : ℝ)))ᴴ *ᵥ
      (fun x => (psi38Z x : ℂ))) s = 0
    rw [mode_create_mulVec_int_cast]
    have h := congrFun (psi38_mode_kernel.1 k) s
    exact_mod_cast h
  · intro k
    funext s
    change (mode (fun j => (modes38Z ⟨k.val + 3, by omega⟩ j : ℝ)) *ᵥ
      (fun x => (psi38Z x : ℂ))) s = 0
    rw [mode_mulVec_int_cast]
    have h := congrFun (psi38_mode_kernel.2 k) s
    exact_mod_cast h
private theorem psi58_complex_mode_kernel :
    (∀ k : Fin 3,
      (mode (fun j => (modes58Z ⟨k.val, by omega⟩ j : ℝ)))ᴴ *ᵥ psi58 = 0) ∧
    (∀ k : Fin 3,
      mode (fun j => (modes58Z ⟨k.val + 3, by omega⟩ j : ℝ)) *ᵥ psi58 = 0) := by
  constructor
  · intro k
    funext s
    change ((mode (fun j => (modes58Z ⟨k.val, by omega⟩ j : ℝ)))ᴴ *ᵥ
      (fun x => (psi58Z x : ℂ))) s = 0
    rw [mode_create_mulVec_int_cast]
    have h := congrFun (psi58_mode_kernel.1 k) s
    exact_mod_cast h
  · intro k
    funext s
    change (mode (fun j => (modes58Z ⟨k.val + 3, by omega⟩ j : ℝ)) *ᵥ
      (fun x => (psi58Z x : ℂ))) s = 0
    rw [mode_mulVec_int_cast]
    have h := congrFun (psi58_mode_kernel.2 k) s
    exact_mod_cast h
private theorem psi38_number :
    numberOperator 6 *ᵥ psi38 = (3 : ℂ) • psi38 := by
  rw [numberOperator_eq_diagonal]
  funext s
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    Pi.smul_apply]
  rw [Finset.sum_eq_single s]
  · simp only []
    change (occupationCount s : ℂ) * psi38 s = (3 : ℂ) * psi38 s
    have h := psi38_three s
    change (∑ j, if s j then (1 : ℤ) else 0) * psi38Z s = 3 * psi38Z s at h
    have hocc : occupationCount s = ∑ j, if s j then 1 else 0 := by
      simp only [occupationCount, Bool.toNat, Bool.cond_eq_ite]
    rw [hocc]
    have hc : ((∑ j, if s j then (1 : ℤ) else 0) : ℂ) * (psi38Z s : ℂ) =
        3 * (psi38Z s : ℂ) := by exact_mod_cast h
    simpa [psi38.eq_1, psi38Z.eq_1] using hc
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))
private theorem psi58_number :
    numberOperator 6 *ᵥ psi58 = (3 : ℂ) • psi58 := by
  rw [numberOperator_eq_diagonal]
  funext s
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
    Pi.smul_apply]
  rw [Finset.sum_eq_single s]
  · simp only []
    change (occupationCount s : ℂ) * psi58 s = (3 : ℂ) * psi58 s
    have h := psi58_three s
    change (∑ j, if s j then (1 : ℤ) else 0) * psi58Z s = 3 * psi58Z s at h
    have hocc : occupationCount s = ∑ j, if s j then 1 else 0 := by
      simp only [occupationCount, Bool.toNat, Bool.cond_eq_ite]
    rw [hocc]
    have hc : ((∑ j, if s j then (1 : ℤ) else 0) : ℂ) * (psi58Z s : ℂ) =
        3 * (psi58Z s : ℂ) := by exact_mod_cast h
    simpa [psi58.eq_1, psi58Z.eq_1] using hc
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))
private theorem psi38_nonzero : psi38 ≠ 0 := by
  intro h
  have hz : psi38Z = 0 := by
    funext x
    have hx := congrFun h x
    change (psi38Z x : ℂ) = 0 at hx
    exact_mod_cast hx
  have hn := psi38_norm
  rw [hz] at hn
  norm_num at hn
private theorem psi58_nonzero : psi58 ≠ 0 := by
  intro h
  have hz : psi58Z = 0 := by
    funext x
    have hx := congrFun h x
    change (psi58Z x : ℂ) = 0 at hx
    exact_mod_cast hx
  have hn := psi58_norm
  rw [hz] at hn
  norm_num at hn
private theorem psi_overlap : star psi58 ⬝ᵥ psi38 = (1152 : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  have hstar (x : Assignment 6) : star (psi58 x) = (psi58Z x : ℂ) := by
    simp [psi58.eq_1, psi58Z.eq_1]
  have hcast (x : Assignment 6) : psi38 x = (psi38Z x : ℂ) := by
    rfl
  simp_rw [hstar, hcast]
  have h := psi38_overlap
  exact_mod_cast h
private def alpha38 : Fin 6 → ℝ := ![11/48, 1/224, 1/672, 1/224, 1/672, 11/48]
private def alpha58 : Fin 6 → ℝ := ![13/48, 1/224, 1/672, 1/224, 1/672, 13/48]
private def B38 (k : Fin 6) : FullOperator 6 :=
  if k.val < 3 then (mode (modes38 k))ᴴ else mode (modes38 k)
private def B58 (k : Fin 6) : FullOperator 6 :=
  if k.val < 3 then (mode (modes58 k))ᴴ else mode (modes58 k)
private theorem hamiltonian_eq_dGamma (N : ℕ) (v : ℝ) :
    hamiltonian N v = dGamma (sshHopping N v) := rfl
private theorem mode_adj_mul {M : ℕ} (l : Fin M → ℝ) :
    (mode l)ᴴ * mode l = ((∑ j, l j ^ 2 : ℝ) : ℂ) • (1 : FullOperator M) -
      mode l * (mode l)ᴴ := by
  exact eq_sub_of_add_eq' (mode_car l)
private theorem sos38 :
    hamiltonian 3 (3/8) = (-25/8 : ℂ) • (1 : FullOperator 6) +
      ∑ k, (alpha38 k : ℂ) • ((B38 k)ᴴ * B38 k) := by
  rw [hamiltonian_eq_dGamma, hopping38, dGamma_sum_smul]
  simp_rw [dGamma_rankOne]
  unfold B38 alpha38 eig38
  simp only [Fin.sum_univ_succ, Fin.isValue]
  rw [mode_adj_mul, mode_adj_mul, mode_adj_mul]
  norm_num [modes38.eq_1, modeNorm.eq_1, Fin.sum_univ_succ, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  module
private theorem sos58 :
    hamiltonian 3 (5/8) = (-27/8 : ℂ) • (1 : FullOperator 6) +
      ∑ k, (alpha58 k : ℂ) • ((B58 k)ᴴ * B58 k) := by
  rw [hamiltonian_eq_dGamma, hopping58, dGamma_sum_smul]
  simp_rw [dGamma_rankOne]
  unfold B58 alpha58 eig58
  simp only [Fin.sum_univ_succ, Fin.isValue]
  rw [mode_adj_mul, mode_adj_mul, mode_adj_mul]
  norm_num [modes58.eq_1, modeNorm.eq_1, Fin.sum_univ_succ, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  module
private def code2 : Assignment 2 ≃ Fin 4 :=
  (Equiv.piCongrRight (fun _ : Fin 2 => finTwoEquiv.symm)).trans
    (finFunctionFinEquiv (m := 2) (n := 2))
private def code4 : Assignment 4 ≃ Fin 16 :=
  (Equiv.piCongrRight (fun _ : Fin 4 => finTwoEquiv.symm)).trans
    (finFunctionFinEquiv (m := 2) (n := 4))
private def reduceInt (X : Assignment 6 → Assignment 6 → ℤ) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  fun a b => ∑ z : Fin 16,
    X (Fin.append (code2.symm a) (code4.symm z))
      (Fin.append (code2.symm b) (code4.symm z))
private def outerInt (f g : Assignment 6 → ℤ) : Assignment 6 → Assignment 6 → ℤ :=
  Matrix.vecMulVec f g
private def r38Int : Matrix (Fin 4) (Fin 4) ℤ :=
  reduceInt (outerInt psi38Z psi58Z)
private def r11Int : Matrix (Fin 4) (Fin 4) ℤ :=
  reduceInt (outerInt psi38Z psi38Z)
private def r22Int : Matrix (Fin 4) (Fin 4) ℤ :=
  reduceInt (outerInt psi58Z psi58Z)

set_option maxRecDepth 100000 in
private theorem r38Int_eq : r38Int = !![256, 0, 0, 0; 0, 320, -192, 0; 0, -192, 320, 0; 0, 0, 0, 256] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    decide +kernel

set_option maxRecDepth 100000 in
private theorem r11Int_eq : r11Int = !![832, 0, 0, 0; 0, 932, -420, 0; 0, -420, 932, 0; 0, 0, 0, 832] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    decide +kernel

set_option maxRecDepth 1000000 in
private theorem r22Int_eq : r22Int = !![80, 0, 0, 0; 0, 116, -84, 0; 0, -84, 116, 0; 0, 0, 0, 80] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem quadratic_nonnegC {M : ℕ} (B : FullOperator M) (φ : Assignment M → ℂ) :
    0 ≤ star φ ⬝ᵥ ((Bᴴ * B) *ᵥ φ) :=
  (Matrix.posSemidef_conjTranspose_mul_self B).dotProduct_mulVec_nonneg φ
private theorem quadratic_nonneg {M : ℕ} (B : FullOperator M) (φ : Assignment M → ℂ) :
    0 ≤ (star φ ⬝ᵥ ((Bᴴ * B) *ᵥ φ)).re :=
  (Matrix.posSemidef_conjTranspose_mul_self B).re_dotProduct_nonneg φ
private theorem sos_lower {K M : ℕ} (E : ℝ) (α : Fin K → ℝ)
    (B : Fin K → FullOperator M) (H : FullOperator M) (φ : Assignment M → ℂ)
    (hs : H = (E : ℂ) • (1 : FullOperator M) +
      ∑ k, (α k : ℂ) • ((B k)ᴴ * B k))
    (ha : ∀ k, 0 ≤ α k) :
    E * (star φ ⬝ᵥ φ).re ≤ (star φ ⬝ᵥ (H *ᵥ φ)).re := by
  rw [hs]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul]
  rw [dotProduct_sum]
  simp_rw [dotProduct_smul]
  have hq (k : Fin K) :
      star φ ⬝ᵥ (((B k)ᴴ * B k) *ᵥ φ) =
        ((star φ ⬝ᵥ (((B k)ᴴ * B k) *ᵥ φ)).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (quadratic_nonnegC (B k) φ)).2.symm
  have hsumEq :
      (∑ x, (α x : ℂ) • (star φ ⬝ᵥ (((B x)ᴴ * B x) *ᵥ φ))) =
        ∑ x, (α x : ℂ) •
          ((star φ ⬝ᵥ (((B x)ᴴ * B x) *ᵥ φ)).re : ℂ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simpa using congrArg (fun z : ℂ => (α k : ℂ) • z) (hq k)
  rw [hsumEq]
  simp only [smul_eq_mul, Complex.add_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsum : 0 ≤ ∑ k, α k * (star φ ⬝ᵥ (((B k)ᴴ * B k) *ᵥ φ)).re := by
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (quadratic_nonneg (B k) φ)
  linarith

private theorem B38_kernel : ∀ k : Fin 6, B38 k *ᵥ psi38 = 0 := by
  have he (k : Fin 6) : modes38 k = fun j => (modes38Z k j : ℝ) := by
    funext j
    fin_cases k <;> fin_cases j <;> norm_num [modes38.eq_1, modes38Z.eq_1]
  intro k
  fin_cases k
  · change (mode (modes38 0))ᴴ *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.1 ⟨0, by omega⟩
  · change (mode (modes38 1))ᴴ *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.1 ⟨1, by omega⟩
  · change (mode (modes38 2))ᴴ *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.1 ⟨2, by omega⟩
  · change mode (modes38 3) *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.2 ⟨0, by omega⟩
  · change mode (modes38 4) *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.2 ⟨1, by omega⟩
  · change mode (modes38 5) *ᵥ psi38 = 0
    rw [he]
    exact psi38_complex_mode_kernel.2 ⟨2, by omega⟩

private theorem B58_kernel : ∀ k : Fin 6, B58 k *ᵥ psi58 = 0 := by
  have he (k : Fin 6) : modes58 k = fun j => (modes58Z k j : ℝ) := by
    funext j
    fin_cases k <;> fin_cases j <;> norm_num [modes58.eq_1, modes58Z.eq_1]
  intro k
  fin_cases k
  · change (mode (modes58 0))ᴴ *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.1 ⟨0, by omega⟩
  · change (mode (modes58 1))ᴴ *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.1 ⟨1, by omega⟩
  · change (mode (modes58 2))ᴴ *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.1 ⟨2, by omega⟩
  · change mode (modes58 3) *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.2 ⟨0, by omega⟩
  · change mode (modes58 4) *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.2 ⟨1, by omega⟩
  · change mode (modes58 5) *ᵥ psi58 = 0
    rw [he]
    exact psi58_complex_mode_kernel.2 ⟨2, by omega⟩

private theorem psi38_energy :
    hamiltonian 3 (3/8) *ᵥ psi38 = (-25/8 : ℂ) • psi38 := by
  rw [sos38]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    Matrix.one_mulVec]
  have hterm (k : Fin 6) :
      (alpha38 k : ℂ) • (((B38 k)ᴴ * B38 k) *ᵥ psi38) = 0 := by
    rw [← Matrix.mulVec_mulVec, B38_kernel k, Matrix.mulVec_zero, smul_zero]
  rw [Finset.sum_eq_zero (fun k hk => hterm k)]
  simp only [add_zero]

private theorem psi58_energy :
    hamiltonian 3 (5/8) *ᵥ psi58 = (-27/8 : ℂ) • psi58 := by
  rw [sos58]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    Matrix.one_mulVec]
  have hterm (k : Fin 6) :
      (alpha58 k : ℂ) • (((B58 k)ᴴ * B58 k) *ᵥ psi58) = 0 := by
    rw [← Matrix.mulVec_mulVec, B58_kernel k, Matrix.mulVec_zero, smul_zero]
  rw [Finset.sum_eq_zero (fun k hk => hterm k)]
  simp only [add_zero]

private theorem alpha38_nonneg : ∀ k : Fin 6, 0 ≤ alpha38 k := by
  intro k
  fin_cases k <;> norm_num [alpha38.eq_1]

private theorem alpha58_nonneg : ∀ k : Fin 6, 0 ≤ alpha58 k := by
  intro k
  fin_cases k <;> norm_num [alpha58.eq_1]

private theorem ground_from_sos (v E : ℝ) (α : Fin 6 → ℝ)
    (B : Fin 6 → FullOperator 6) (H : FullOperator 6) (ψ : Assignment 6 → ℂ)
    (hH : H = hamiltonian 3 v)
    (hs : H = (E : ℂ) • (1 : FullOperator 6) +
      ∑ k, (α k : ℂ) • ((B k)ᴴ * B k))
    (ha : ∀ k, 0 ≤ α k) (hψ : ψ ≠ 0)
    (hnum : numberOperator 6 *ᵥ ψ = (3 : ℂ) • ψ)
    (henergy : H *ᵥ ψ = (E : ℂ) • ψ) :
    IsHalfFilledGroundState 3 v ψ := by
  refine ⟨hψ, hnum, ?_⟩
  intro φ hφ hφnum
  have hl := sos_lower E α B H φ hs ha
  have hnorm : 0 ≤ (star ψ ⬝ᵥ ψ).re :=
    (Complex.nonneg_iff.mp (dotProduct_star_self_nonneg ψ)).1
  have hm := mul_le_mul_of_nonneg_right hl hnorm
  have he : (star ψ ⬝ᵥ (H *ᵥ ψ)).re = E * (star ψ ⬝ᵥ ψ).re := by
    rw [henergy]
    rw [dotProduct_smul]
    simp [Complex.mul_re]
  rw [← hH, he]
  nlinarith

private theorem ground38 : IsHalfFilledGroundState 3 (3/8) psi38 :=
  ground_from_sos (3/8) (-25/8) alpha38 B38 (hamiltonian 3 (3/8)) psi38
    rfl (by convert sos38 using 1; norm_num) alpha38_nonneg psi38_nonzero
    psi38_number (by convert psi38_energy using 1; norm_num)

private theorem ground58 : IsHalfFilledGroundState 3 (5/8) psi58 :=
  ground_from_sos (5/8) (-27/8) alpha58 B58 (hamiltonian 3 (5/8)) psi58
    rfl (by convert sos58 using 1; norm_num) alpha58_nonneg psi58_nonzero
    psi58_number (by convert psi58_energy using 1; norm_num)

private theorem reduce_three_one (X : FullOperator 6) (a b : Assignment 2) :
    reduce (by norm_num : 2 * 1 ≤ 2 * 3) X a b =
      ∑ z : Assignment 4, X (Fin.append a z) (Fin.append b z) := by
  unfold reduce
  simp_rw [← (Fin.appendEquiv (α := Bool) 2 4).sum_comp]
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk]
  simp_rw [Fin.append_left']
  simp only [Nat.reduceMul]
  have hleftAll (x y : Assignment 2) :
      (∀ i : Fin 2, x i = y i) ↔ x = y := funext_iff.symm
  have htail (x y : Assignment 2 × Assignment 4) :
      (∀ k : Fin 6, 2 ≤ k.val →
        Fin.append x.1 x.2 k = Fin.append y.1 y.2 k) ↔ x.2 = y.2 := by
    constructor
    · intro h
      funext i
      have hi := h (Fin.natAdd 2 i) (by simp)
      simpa using hi
    · intro h k hk
      fin_cases k
      · norm_num at hk
      · norm_num at hk
      · change x.2 0 = y.2 0
        exact congrFun h ⟨0, by omega⟩
      · change x.2 1 = y.2 1
        exact congrFun h ⟨1, by omega⟩
      · change x.2 2 = y.2 2
        exact congrFun h ⟨2, by omega⟩
      · change x.2 3 = y.2 3
        exact congrFun h ⟨3, by omega⟩
  simp_rw [hleftAll, htail]
  have hinner (x : Assignment 2 × Assignment 4) :
      (∑ y : Assignment 2 × Assignment 4,
        if x.1 = a ∧ y.1 = b ∧ x.2 = y.2 then
          X (Fin.append x.1 x.2) (Fin.append y.1 y.2) else 0) =
        if x.1 = a then X (Fin.append x.1 x.2) (Fin.append b x.2) else 0 := by
    by_cases hxa : x.1 = a
    · rw [if_pos hxa]
      rw [Finset.sum_eq_single (b, x.2)]
      · simp [hxa]
      · intro y hy hne
        have hy' : ¬ (y.1 = b ∧ x.2 = y.2) := by
          intro hh
          apply hne
          rcases y with ⟨y1, y2⟩
          simp_all [Prod.ext_iff]
        simp [hxa, hy']
      · simp
    · simp [hxa]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', Finset.sum_ite_irrel]

private theorem sum_cast_outer (f g : Assignment 6 → ℤ) (a b : Assignment 2) :
    (∑ z : Assignment 4,
      ((f (Fin.append a z) * g (Fin.append b z) : ℤ) : ℂ)) =
      (reduceInt (outerInt f g) (code2 a) (code2 b) : ℂ) := by
  unfold reduceInt outerInt
  rw [← code4.sum_comp]
  simp only [Equiv.symm_apply_apply, Int.cast_sum, Matrix.vecMulVec_apply]

private theorem reduced_cast (f g : Assignment 6 → ℤ) (t : ℂ) :
    reduce (by norm_num : 2 * 1 ≤ 2 * 3)
      (t • Matrix.vecMulVec (fun x => (f x : ℂ)) (star (fun x => (g x : ℂ)))) =
      fun a b => t * (reduceInt (outerInt f g) (code2 a) (code2 b) : ℂ) := by
  ext a b
  rw [reduce_three_one]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Pi.star_apply, star_intCast, ← Int.cast_mul, ← Finset.mul_sum, sum_cast_outer]

private theorem psi_norms :
    star psi38 ⬝ᵥ psi38 = (3528 : ℂ) ∧ star psi58 ⬝ᵥ psi58 = (392 : ℂ) := by
  constructor
  · change (∑ x, star (psi38Z x : ℂ) * (psi38Z x : ℂ)) = _
    simp only [star_intCast, ← pow_two]
    exact_mod_cast psi38_norm
  · change (∑ x, star (psi58Z x : ℂ) * (psi58Z x : ℂ)) = _
    simp only [star_intCast, ← pow_two]
    exact_mod_cast psi58_norm

private def block (a p q : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![a, 0, 0, 0; 0, p, q, 0; 0, q, p, 0; 0, 0, 0, a]

private theorem reduced38 :
    reduce (by norm_num : 2 * 1 ≤ 2 * 3)
      ((star psi58 ⬝ᵥ psi38)⁻¹ • Matrix.vecMulVec psi38 (star psi58)) =
      fun a b => block (2/9) (5/18) (-1/6) (code2 a) (code2 b) := by
  rw [psi_overlap]
  change reduce (N := 3) (L := 1) _ ((1152 : ℂ)⁻¹ • Matrix.vecMulVec
    (fun x => (psi38Z x : ℂ)) (star (fun x => (psi58Z x : ℂ)))) = _
  rw [reduced_cast]
  have hr := r38Int_eq
  change reduceInt (outerInt psi38Z psi58Z) = _ at hr
  rw [hr]
  ext a b
  generalize code2 a = i
  generalize code2 b = j
  fin_cases i <;> fin_cases j <;> norm_num [block.eq_1]

private theorem reduced11 :
    reduce (by norm_num : 2 * 1 ≤ 2 * 3)
      ((star psi38 ⬝ᵥ psi38)⁻¹ • Matrix.vecMulVec psi38 (star psi38)) =
      fun a b => block (104/441) (233/882) (-5/42) (code2 a) (code2 b) := by
  rw [psi_norms.1]
  change reduce (N := 3) (L := 1) _ ((3528 : ℂ)⁻¹ • Matrix.vecMulVec
    (fun x => (psi38Z x : ℂ)) (star (fun x => (psi38Z x : ℂ)))) = _
  rw [reduced_cast]
  have hr := r11Int_eq
  change reduceInt (outerInt psi38Z psi38Z) = _ at hr
  rw [hr]
  ext a b
  generalize code2 a = i
  generalize code2 b = j
  fin_cases i <;> fin_cases j <;> norm_num [block.eq_1]

private theorem reduced22 :
    reduce (by norm_num : 2 * 1 ≤ 2 * 3)
      ((star psi58 ⬝ᵥ psi58)⁻¹ • Matrix.vecMulVec psi58 (star psi58)) =
      fun a b => block (10/49) (29/98) (-3/14) (code2 a) (code2 b) := by
  rw [psi_norms.2]
  change reduce (N := 3) (L := 1) _ ((392 : ℂ)⁻¹ • Matrix.vecMulVec
    (fun x => (psi58Z x : ℂ)) (star (fun x => (psi58Z x : ℂ)))) = _
  rw [reduced_cast]
  have hr := r22Int_eq
  change reduceInt (outerInt psi58Z psi58Z) = _ at hr
  rw [hr]
  ext a b
  generalize code2 a = i
  generalize code2 b = j
  fin_cases i <;> fin_cases j <;> norm_num [block.eq_1]

private theorem block_entropy (a p q : ℝ) (ha : 0 < a)
    (hp : 0 < p + q) (hq : 0 < p - q) :
    (matrixEntropy (fun x y => block (a : ℂ) p q (code2 x) (code2 y))).re =
      -(2 * a * Real.log a + (p + q) * Real.log (p + q) +
        (p - q) * Real.log (p - q)) := by
  let P : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, -1, 0; 0, 0, 0, 1]
  let Q : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, 0, 0, 0; 0, 1/2, 1/2, 0; 0, 1/2, -1/2, 0; 0, 0, 0, 1]
  let d : Fin 4 → ℂ := ![a, (p + q : ℝ), (p - q : ℝ), a]
  have hQP : Q * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P, Q, Matrix.mul_apply, Fin.sum_univ_succ]
  have hs : P * Matrix.diagonal d * Q = block a p q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, d, block.eq_1, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Matrix.diagonal_apply, Fin.sum_univ_succ] <;> ring
  have hc : (show FullOperator 2 from
      fun x y => block (a : ℂ) p q (code2 x) (code2 y)).charpoly =
      (Matrix.diagonal d).charpoly := by
    change (Matrix.reindex code2.symm code2.symm (block a p q)).charpoly = _
    rw [Matrix.charpoly_reindex, ← hs, Matrix.charpoly_mul_comm (P * Matrix.diagonal d) Q,
      ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hr : (Matrix.diagonal d).charpoly.roots =
      ({(a : ℂ), ((p + q : ℝ) : ℂ), ((p - q : ℝ) : ℂ), (a : ℂ)} : Multiset ℂ) := by
    rw [Matrix.charpoly_diagonal]
    have he : (∏ i : Fin 4, (Polynomial.X - Polynomial.C (d i))) =
        (({(a : ℂ), ((p + q : ℝ) : ℂ), ((p - q : ℝ) : ℂ), (a : ℂ)} :
          Multiset ℂ).map (fun z => Polynomial.X - Polynomial.C z)).prod := by
      simp [d, Fin.prod_univ_succ, Multiset.insert_eq_cons]
    rw [he, Polynomial.roots_multiset_prod_X_sub_C]
  unfold matrixEntropy
  rw [hc, hr]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton, ← Complex.ofReal_log ha.le,
    ← Complex.ofReal_log hp.le, ← Complex.ofReal_log hq.le, Complex.add_re,
    Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

private theorem entropy38 :
    (matrixEntropy (fun a b => block (2/9) (5/18) (-1/6) (code2 a) (code2 b))).re =
      2 * Real.log 3 - (4/3) * Real.log 2 := by
  have h := block_entropy (2/9) (5/18) (-1/6) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  rw [h]
  simp (disch := norm_num) only [Real.log_div, Real.log_one]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    convert Real.log_pow (3 : ℝ) 2 using 1 <;> norm_num
  rw [h4, h9]
  ring

private theorem entropy11 :
    (matrixEntropy (fun a b => block (104/441) (233/882) (-5/42)
      (code2 a) (code2 b))).re =
      2 * Real.log 3 + 2 * Real.log 7 - (16/7) * Real.log 2 - (26/21) * Real.log 13 := by
  have h := block_entropy (104/441) (233/882) (-5/42)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  rw [h]
  simp (disch := norm_num) only [Real.log_div]
  have h104 : Real.log (104 : ℝ) = 3 * Real.log 2 + Real.log 13 := by
    calc
      Real.log (104 : ℝ) = Real.log ((2 : ℝ)^3 * 13) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have h441 : Real.log (441 : ℝ) = 2 * Real.log 3 + 2 * Real.log 7 := by
    calc
      Real.log (441 : ℝ) = Real.log ((3 : ℝ)^2 * 7^2) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
                  norm_num
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 6 using 1 <;> norm_num
  have h169 : Real.log (169 : ℝ) = 2 * Real.log 13 := by
    convert Real.log_pow (13 : ℝ) 2 using 1 <;> norm_num
  rw [h104, h441, h64, h169]
  ring

private theorem entropy22 :
    (matrixEntropy (fun a b => block (10/49) (29/98) (-3/14) (code2 a) (code2 b))).re =
      2 * Real.log 7 - (4/7) * Real.log 2 - (10/7) * Real.log 5 := by
  have h := block_entropy (10/49) (29/98) (-3/14) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h ⊢
  rw [h]
  simp (disch := norm_num) only [Real.log_div]
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    convert Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (5 : ℝ) ≠ 0) using 1; norm_num
  have h49 : Real.log (49 : ℝ) = 2 * Real.log 7 := by
    convert Real.log_pow (7 : ℝ) 2 using 1 <;> norm_num
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  have h25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    convert Real.log_pow (5 : ℝ) 2 using 1 <;> norm_num
  rw [h10, h49, h4, h25]
  ring

private theorem excess_positive :
    0 < averagedExcess (by norm_num : 2 * 1 ≤ 2 * 3) psi38 psi58 := by
  unfold averagedExcess
  rw [reduced38, reduced11, reduced22, entropy38, entropy11, entropy22]
  have hn : (7 : ℕ)^42 < 2^2 * 3^21 * 5^15 * 13^13 := by norm_num
  have hr : (7 : ℝ)^42 < 2^2 * 3^21 * 5^15 * 13^13 := by exact_mod_cast hn
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < 7^42) hr
  simp (disch := positivity) only [Real.log_mul, Real.log_pow] at hl
  norm_num at hl
  linarith

theorem result : ¬ claim := by
  intro hc
  have h := hc 3 1 (by norm_num) (by norm_num) (by norm_num)
    (3/8) (5/8) (Or.inl (by norm_num)) psi38 psi58 ground38 ground58
    (by rw [psi_overlap]; norm_num)
  exact (not_le_of_gt excess_positive) h

end
end D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
