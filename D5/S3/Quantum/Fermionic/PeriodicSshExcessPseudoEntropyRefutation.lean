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

private theorem fullC_entry {M : ℕ} (j : Fin M) (s t : Assignment M) :
    fullC j s t =
      if t j = true ∧ s = Function.update t j false
      then (-1 : ℂ) ^ prefixCount t j else 0 := by
  classical
  rw [fullC_entries]
  by_cases h : t j = true ∧ s = Function.update t j false
  · rw [if_pos h]
    have he : (∏ i : Fin M, fermionWord j i (s i) (t i)) =
        ∏ i : Fin M, if i < j ∧ t i = true then (-1 : ℂ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [h.2]
      by_cases hij : i < j
      · have hne : i ≠ j := ne_of_lt hij
        simp only [fermionWord, if_pos hij, Function.update_of_ne hne]
        cases t i <;>
          simp [hij, D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv,
            Matrix.diagonal_apply]
      · by_cases heq : i = j
        · subst i
          simp [fermionWord, Matrix.single, h.1]
        · simp [fermionWord, hij, heq, Matrix.one_apply, Function.update_of_ne heq]
    rw [he, ← Finset.prod_filter]
    simp [prefixCount, Finset.prod_const]
  · rw [if_neg h]
    by_cases ht : t j = true
    · have hs : s ≠ Function.update t j false := by tauto
      have hx : ∃ i, s i ≠ Function.update t j false i := by
        by_contra hh
        push Not at hh
        exact hs (funext hh)
      obtain ⟨i, hi⟩ := hx
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_cases heq : i = j
      · subst i
        simp only [Function.update_self] at hi
        have hsi : s j = true := by cases hsj : s j <;> simp_all
        simp [fermionWord, Matrix.single, hsi]
      · have hst : s i ≠ t i := by simpa only [Function.update_of_ne heq] using hi
        by_cases hij : i < j
        · simp only [fermionWord, if_pos hij]
          cases hsi : s i <;> cases hti : t i <;>
            try { exfalso; apply hst; simp [hsi, hti] }
          all_goals
            simp [D5.S3.Quantum.FiniteDimensional.qubitZ, finTwoEquiv,
              Matrix.diagonal_apply, hsi, hti]
        · simp [fermionWord, hij, heq, hst, Matrix.one_apply]
    · apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [fermionWord, Matrix.single, ht]

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
        simp [h.1, hs] at this
      rw [if_neg hcond]
      simp
  · intro b hb hne
    rw [fullC_entry]
    by_cases hs : s j = false
    · have hfalse : ¬(b j = true ∧ s = Function.update b j false) := by
        intro h
        apply hne
        funext i
        by_cases hij : i = j
        · subst i
          simp [h.1]
        · have hi := congrFun h.2 i
          simp only [Function.update_of_ne hij] at hi
          simp [Function.update_of_ne hij, hi]
      simp [hfalse]
    · have hfalse : s j = true := by cases hsj : s j <;> simp_all
      have hfalse' : ¬(b j = true ∧ s = Function.update b j false) := by
        intro h
        have := congrFun h.2 j
        simp [h.1, hfalse] at this
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
    by_cases h : s j = true ∧ t = Function.update s j false
    · have hp : prefixCount t j = prefixCount s j := by
        rw [h.2]
        unfold prefixCount
        congr 1
        ext i
        by_cases hij : i < j
        · have hne : i ≠ j := ne_of_lt hij
          simp [hij, Function.update_of_ne hne]
        · simp [hij]
      simp [h, hp]
    · simp [h]
  rw [Finset.sum_eq_single (Function.update s j false)]
  · rw [hentry]
    by_cases hs : s j = true
    · rw [if_pos hs]
      have hp : prefixCount (Function.update s j false) j = prefixCount s j := by
        unfold prefixCount
        congr 1
        ext i
        by_cases hij : i < j
        · have hne : i ≠ j := ne_of_lt hij
          simp [hij, Function.update_of_ne hne]
        · simp [hij]
      simp [hs, hp]
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

private theorem mode_mulVec_int_cast (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ)
    (s : Assignment 6) :
    (mode (fun j => (l j : ℝ)) *ᵥ (fun x => (f x : ℂ))) s =
      (modeInt l f s : ℂ) := by
  classical
  simp only [mode, Matrix.sum_mulVec, Matrix.smul_mulVec]
  simp [fullC_sparse]
  unfold modeInt
  push_cast
  simp [Complex.ofReal_mul]

private theorem mode_create_mulVec_int_cast (l : Fin 6 → ℤ) (f : Assignment 6 → ℤ)
    (s : Assignment 6) :
    ((mode (fun j => (l j : ℝ)))ᴴ *ᵥ (fun x => (f x : ℂ))) s =
      (modeCreateInt l f s : ℂ) := by
  classical
  simp only [mode, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.conjTranspose_apply]
  simp [fullC_create_sparse]
  unfold modeCreateInt
  push_cast
  simp [Complex.ofReal_mul]

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
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, if_pos rfl,
    one_mul, Pi.smul_apply]
  rw [Finset.sum_eq_single s]
  · simp only [if_pos rfl, one_mul, Pi.smul_apply]
    change (occupationCount s : ℂ) * psi38 s = (3 : ℂ) * psi38 s
    have h := psi38_three s
    change (∑ j, if s j then (1 : ℤ) else 0) * psi38Z s = 3 * psi38Z s at h
    have hocc : occupationCount s = ∑ j, if s j then 1 else 0 := by
      unfold occupationCount
      apply Finset.sum_congr rfl
      intro j hj
      cases hs : s j <;> simp [hs]
    rw [hocc]
    have hc : ((∑ j, if s j then (1 : ℤ) else 0) : ℂ) * (psi38Z s : ℂ) =
        3 * (psi38Z s : ℂ) := by exact_mod_cast h
    simpa [psi38, psi38Z] using hc
  · intro b hb hne
    simp [Ne.symm hne]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))

private theorem psi58_number :
    numberOperator 6 *ᵥ psi58 = (3 : ℂ) • psi58 := by
  rw [numberOperator_eq_diagonal]
  funext s
  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, if_pos rfl,
    one_mul, Pi.smul_apply]
  rw [Finset.sum_eq_single s]
  · simp only [if_pos rfl, one_mul, Pi.smul_apply]
    change (occupationCount s : ℂ) * psi58 s = (3 : ℂ) * psi58 s
    have h := psi58_three s
    change (∑ j, if s j then (1 : ℤ) else 0) * psi58Z s = 3 * psi58Z s at h
    have hocc : occupationCount s = ∑ j, if s j then 1 else 0 := by
      unfold occupationCount
      apply Finset.sum_congr rfl
      intro j hj
      cases hs : s j <;> simp [hs]
    rw [hocc]
    have hc : ((∑ j, if s j then (1 : ℤ) else 0) : ℂ) * (psi58Z s : ℂ) =
        3 * (psi58Z s : ℂ) := by exact_mod_cast h
    simpa [psi58, psi58Z] using hc
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
    simp [psi58, psi58Z]
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

private theorem modes38_norm : ∀ k : Fin 6, ∑ x, modes38 k x ^ 2 = modeNorm k := by
  intro k
  fin_cases k <;> norm_num [modes38, modeNorm, Fin.sum_univ_succ]

private theorem modes58_norm : ∀ k : Fin 6, ∑ x, modes58 k x ^ 2 = modeNorm k := by
  intro k
  fin_cases k <;> norm_num [modes58, modeNorm, Fin.sum_univ_succ]

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
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.mk.injEq, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceIte]
  rw [mode_adj_mul, mode_adj_mul, mode_adj_mul]
  norm_num [modes38, modeNorm, Fin.sum_univ_succ, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  module

private theorem sos58 :
    hamiltonian 3 (5/8) = (-27/8 : ℂ) • (1 : FullOperator 6) +
      ∑ k, (alpha58 k : ℂ) • ((B58 k)ᴴ * B58 k) := by
  rw [hamiltonian_eq_dGamma, hopping58, dGamma_sum_smul]
  simp_rw [dGamma_rankOne]
  unfold B58 alpha58 eig58
  simp only [Fin.sum_univ_succ, Fin.isValue, Fin.mk.injEq, Nat.reduceAdd, Nat.reduceLT,
    ↓reduceIte]
  rw [mode_adj_mul, mode_adj_mul, mode_adj_mul]
  norm_num [modes58, modeNorm, Fin.sum_univ_succ, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail]
  module

private def reduceInt (X : Assignment 6 → Assignment 6 → ℤ) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  fun a b => ∑ z : Fin 16,
    X (Fin.append (finFunctionFinEquiv.symm a) (finFunctionFinEquiv.symm z))
      (Fin.append (finFunctionFinEquiv.symm b) (finFunctionFinEquiv.symm z))

private def outerInt (f g : Assignment 6 → ℤ) : Assignment 6 → Assignment 6 → ℤ :=
  fun x y => f x * g y

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
  fin_cases i <;> fin_cases j <;>
    simp [r22Int, reduceInt, outerInt, psi58Z, psi58, psiCode,
      Fin.sum_univ_succ, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_two]

theorem result : ¬ claim := by
  sorry

end
end D5.S3.Quantum.Fermionic.PeriodicSshExcessPseudoEntropyRefutation
