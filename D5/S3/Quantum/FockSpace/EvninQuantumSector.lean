/- GID: D5/S3/Quantum/FockSpace/EvninQuantumSector
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/EvninQuantumSector
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted normal-ordered Hamiltonian in Evnin's finite occupation sectors. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.WeightedBond.LagrangeBurmann
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The normalized occupation model for Evnin, arXiv:2607.25445v3, §2.3. -/

compile_only_with_mathlib

set_option autoImplicit false
open scoped BigOperators Matrix ComplexOrder
open Finset

namespace D5.S3.Quantum.FockSpace.EvninQuantumSector
noncomputable section

/-- The ordered double sum of pair defects for a finite family of rectangular
matrices and arbitrary real weights. The row index may be empty. -/
private theorem weighted_gram_defect {ι ρ κ : Type*} [Fintype ρ] (s : Finset ι)
    (w : ι → ℝ) (b : ι → Matrix ρ κ ℂ) :
    let B := ∑ i ∈ s, w i • b i
    let D := fun i j => w i • b j - w j • b i
    ∑ i ∈ s, ∑ j ∈ s, (D i j)ᴴ * D i j =
      2 • ((∑ i ∈ s, w i ^ 2) • (∑ i ∈ s, (b i)ᴴ * b i) - Bᴴ * B) := by
  classical
  dsimp only
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  simp_rw [Matrix.mul_sum, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have diag :
      (∑ i ∈ s, ∑ j ∈ s, w i ^ 2 • ((b j)ᴴ * b j)) =
        (∑ i ∈ s, w i ^ 2) • (∑ j ∈ s, (b j)ᴴ * b j) := by
    rw [sum_smul]
    apply sum_congr rfl
    intro i _
    rw [smul_sum]
  have diag_swap :
      (∑ i ∈ s, ∑ j ∈ s, w j ^ 2 • ((b i)ᴴ * b i)) =
        (∑ i ∈ s, w i ^ 2) • (∑ j ∈ s, (b j)ᴴ * b j) :=
    Finset.sum_comm.trans diag
  have cross :
      (∑ i ∈ s, ∑ j ∈ s, (w i * w j) • ((b j)ᴴ * b i)) =
        ∑ i ∈ s, ∑ j ∈ s, (w i * w j) • ((b i)ᴴ * b j) := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have expand (i j : ι) :
      (w i • b j - w j • b i)ᴴ * (w i • b j - w j • b i) =
        w i ^ 2 • ((b j)ᴴ * b j) + w j ^ 2 • ((b i)ᴴ * b i) -
          (w i * w j) • ((b i)ᴴ * b j) - (w i * w j) • ((b j)ᴴ * b i) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
      pow_two, mul_comm (w j) (w i)]
    abel
  simp only [expand, sum_sub_distrib, sum_add_distrib]
  rw [diag, diag_swap, cross]
  abel

/-- Number of ordered removals from two modes, with the correction for equal modes. -/
private def pairCount {ι : Type*} [DecidableEq ι] (η : ι → ℕ) (i j : ι) : ℝ :=
  (η i : ℝ) * (η j - if i = j then (1 : ℝ) else 0)

private theorem pairCount_eq_zero_of_momentum_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode η : ι → ℕ) (i j : ι) (h : (∑ a, mode a * η a) < mode i + mode j) :
    pairCount η i j = 0 := by
  by_contra hq
  by_cases hij : i = j
  · subst j
    have hi : 2 ≤ η i := by
      by_contra! hlt
      have hsmall : η i = 0 ∨ η i = 1 := by omega
      rcases hsmall with hz | ho
      · exact hq (by simp [pairCount, hz])
      · exact hq (by simp [pairCount, ho])
    have hle : mode i * η i ≤ ∑ a, mode a * η a :=
      single_le_sum (f := fun a => mode a * η a) (fun _ _ => Nat.zero_le _) (mem_univ i)
    have : mode i * 2 ≤ mode i * η i := Nat.mul_le_mul_left _ hi
    omega
  · have hi : 1 ≤ η i := by
      by_contra! hlt
      have hz : η i = 0 := by omega
      exact hq (by simp [pairCount, hz])
    have hj : 1 ≤ η j := by
      by_contra! hlt
      have hz : η j = 0 := by omega
      exact hq (by simp [pairCount, hij, hz])
    have hle : (∑ a ∈ ({i, j} : Finset ι), mode a) ≤ ∑ a, mode a * η a := by
      calc
        (∑ a ∈ ({i, j} : Finset ι), mode a) ≤
            ∑ a ∈ ({i, j} : Finset ι), mode a * η a := by
          apply sum_le_sum
          intro a ha
          have ha' : 1 ≤ η a := by
            simp only [mem_insert, mem_singleton] at ha
            rcases ha with rfl | rfl
            · exact hi
            · exact hj
          simpa using Nat.mul_le_mul_left (mode a) ha'
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    simp [hij] at hle
    omega

/-- The cutoff ordered occupation sum gives the proposed scalar diagonal for all
real weights `σ`, including the repeated-mode correction and the vacuum. -/
private theorem occupation_diagonal_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mode η : ι → ℕ) (N M : ℕ) (hN : ∑ i, η i = N) (hM : ∑ i, mode i * η i = M)
    (σ : ℝ) :
    (∑ i, ∑ j with mode i + mode j ≤ M,
      (1 + σ * (mode i + mode j : ℕ)) * pairCount η i j) / 2 =
        ((N : ℝ) - 1) * (N + 2 * σ * M) / 2 := by
  have count : (∑ i, (η i : ℝ)) = N := by exact_mod_cast hN
  have momentum : (∑ i, (mode i : ℝ) * η i) = M := by exact_mod_cast hM
  have remove_cutoff (i : ι) :
      (∑ j with mode i + mode j ≤ M,
        (1 + σ * (mode i + mode j : ℕ)) * pairCount η i j) =
      ∑ j, (1 + σ * (mode i + mode j : ℕ)) * pairCount η i j := by
    rw [sum_filter]
    apply sum_congr rfl
    intro j _
    by_cases h : mode i + mode j ≤ M
    · simp [h]
    · simp [h, pairCount_eq_zero_of_momentum_lt mode η i j (hM ▸ Nat.lt_of_not_ge h)]
  have row_sum (i : ι) :
      (∑ j, (1 + σ * (mode i + mode j : ℕ)) * pairCount η i j) =
        (η i : ℝ) * ((1 + σ * mode i) * N + σ * M - (1 + 2 * σ * mode i)) := by
    have term (j : ι) :
        (1 + σ * (mode i + mode j : ℕ)) * pairCount η i j =
          (η i : ℝ) * ((1 + σ * mode i) * η j + σ * ((mode j : ℝ) * η j) -
            if i = j then (1 + 2 * σ * mode i) else 0) := by
      by_cases hij : i = j
      · subst j
        simp [pairCount]
        ring
      · simp [pairCount, hij]
        ring
    calc
      _ = (η i : ℝ) * ∑ j, ((1 + σ * mode i) * η j + σ * ((mode j : ℝ) * η j) -
          if i = j then (1 + 2 * σ * mode i) else 0) := by simp only [term, mul_sum]
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
        simp [count, momentum]
  simp_rw [remove_cutoff, row_sum]
  have term (i : ι) :
      (η i : ℝ) * ((1 + σ * mode i) * N + σ * M - (1 + 2 * σ * mode i)) =
        ((N : ℝ) + σ * M - 1) * η i + (σ * (N - 2)) * ((mode i : ℝ) * η i) := by
    ring
  simp only [term, sum_add_distrib, ← mul_sum, count, momentum]
  ring

/-- The first `L+1` modes, shared by the input and output sectors. -/
abbrev Mode (L : ℕ) := Fin (L + 1)

/-- Occupations of fixed particle number and momentum within the ambient mode list. -/
def Sector (L N M : ℕ) :=
  {η : Mode L → ℕ // (∑ a, η a) = N ∧ (∑ a, a.val * η a) = M}

instance (L N M : ℕ) : Fintype (Sector L N M) :=
  Fintype.ofInjective
    (fun (η : Sector L N M) a => (⟨η.val a, by
      have h : η.val a ≤ ∑ b, η.val b :=
        single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)
      rw [η.property.1] at h
      omega⟩ : Fin (N + 1)))
    (fun _ _ h => Subtype.ext (funext fun a => congrArg Fin.val (congrFun h a)))

instance (L N M : ℕ) : DecidableEq (Sector L N M) := Classical.decEq _

private def increment {L : ℕ} (i j a : Mode L) : ℕ :=
  (if a = i then 1 else 0) + if a = j then 1 else 0

private theorem sum_increment {L : ℕ} (i j : Mode L) :
    (∑ a, increment i j a) = 2 := by
  simp [increment, sum_add_distrib]

private theorem momentum_increment {L : ℕ} (i j : Mode L) :
    (∑ a, a.val * increment i j a) = i.val + j.val := by
  simp [increment, mul_add, sum_add_distrib, mul_ite]

private theorem pairCount_nonneg {L : ℕ} (η : Mode L → ℕ) (i j : Mode L) :
    0 ≤ pairCount η i j := by
  by_cases h : i = j
  · subst j
    by_cases hzero : η i = 0
    · simp [pairCount, hzero]
    · have : (1 : ℝ) ≤ η i := by exact_mod_cast (show 1 ≤ η i by omega)
      exact mul_nonneg (Nat.cast_nonneg _) (by simpa using sub_nonneg.mpr this)
  · simp [pairCount, h, mul_nonneg, Nat.cast_nonneg]

private theorem pairCount_zero_of_not_le {L : ℕ} (η : Mode L → ℕ) (i j : Mode L)
    (h : ¬ ∀ a, increment i j a ≤ η a) : pairCount η i j = 0 := by
  push Not at h
  obtain ⟨a, ha⟩ := h
  by_cases hij : i = j
  · subst j
    by_cases hai : a = i
    · subst a
      have hlt : η i < 2 := by simpa [increment] using ha
      rcases (show η i = 0 ∨ η i = 1 by omega) with he | he <;> simp [pairCount, he]
    · simp [increment, hai] at ha
  · by_cases hai : a = i
    · subst a
      have : η i = 0 := by simpa [increment, hij] using ha
      simp [pairCount, this]
    · by_cases haj : a = j
      · subst a
        have : η j = 0 := by simpa [increment, hai] using ha
        simp [pairCount, hij, this]
      · simp [increment, hai, haj] at ha

private def raise {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) (ζ : Sector L (N - 2) (M - (i.val + j.val))) :
    Sector L N M :=
  ⟨fun a => ζ.val a + increment i j a, by
    constructor
    · simp only [sum_add_distrib, ζ.property.1, sum_increment]
      omega
    · simp only [mul_add, sum_add_distrib, ζ.property.2, momentum_increment]
      omega⟩

/-- Matrix of the ordered pair annihilator on the normalized occupation basis. -/
def pairAnnihilator {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) :
    Matrix (Sector L (N - 2) (M - (i.val + j.val))) (Sector L N M) ℂ :=
  fun ζ η => if raise hN i j hM ζ = η then (Real.sqrt (pairCount η.val i j) : ℂ) else 0

private theorem raise_injective {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) : Function.Injective (raise hN i j hM) := by
  intro ζ ξ h
  apply Subtype.ext
  funext a
  exact Nat.add_right_cancel (congrArg (fun η : Sector L N M => η.val a) h)

private theorem exists_raise {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) (η : Sector L N M)
    (h : ∀ a, increment i j a ≤ η.val a) :
    ∃ ζ, raise hN i j hM ζ = η := by
  let z := fun a => η.val a - increment i j a
  have hz (a : Mode L) : z a + increment i j a = η.val a := Nat.sub_add_cancel (h a)
  have hcount := congrArg (fun f : Mode L → ℕ => ∑ a, f a) (funext hz)
  have hmomentum :=
    congrArg (fun f : Mode L → ℕ => ∑ a, a.val * f a) (funext hz)
  simp only [sum_add_distrib, sum_increment, η.property.1] at hcount
  simp only [mul_add, sum_add_distrib, momentum_increment, η.property.2] at hmomentum
  exact ⟨⟨z, by omega, by omega⟩, Subtype.ext (funext hz)⟩

/-- The normalized ladder coefficients square to the ordered removal count.
The equality holds for the same mode twice and for a zero-dimensional output sector. -/
private theorem pair_adjoint_square {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) :
    (pairAnnihilator hN i j hM)ᴴ * pairAnnihilator hN i j hM =
      Matrix.diagonal (fun η => (pairCount η.val i j : ℂ)) := by
  classical
  ext η ξ
  rw [Matrix.mul_apply]
  by_cases he : η = ξ
  · subst ξ
    rw [Matrix.diagonal_apply_eq]
    by_cases h : ∀ a, increment i j a ≤ η.val a
    · obtain ⟨ζ, hζ⟩ := exists_raise hN i j hM η h
      rw [sum_eq_single ζ]
      · simp [Matrix.conjTranspose_apply, pairAnnihilator, hζ,
          ← Complex.ofReal_mul, Real.mul_self_sqrt (pairCount_nonneg η.val i j)]
      · intro ξ _ hξ
        have hh : raise hN i j hM ξ ≠ η :=
          fun hh => hξ (raise_injective hN i j hM (hh.trans hζ.symm))
        simp [pairAnnihilator, hh]
      · simp
    · have hq := pairCount_zero_of_not_le η.val i j h
      simp [pairAnnihilator, hq]
  · rw [Matrix.diagonal_apply_ne _ he]
    apply sum_eq_zero
    intro ζ _
    by_cases hζ : raise hN i j hM ζ = η
    · simp [Matrix.conjTranspose_apply, pairAnnihilator, hζ, he]
    · simp [Matrix.conjTranspose_apply, pairAnnihilator, hζ]

/-- Factorial coordinates of the common pair-lowering vector. -/
private def coordinate {L : ℕ} (A : ℕ → ℝ) (η : Mode L → ℕ) : ℝ :=
  ∏ a, Real.sqrt (A a.val) ^ η a / Real.sqrt (η a).factorial

/-- The attaining vector in the normalized occupation basis. -/
def occupationVector {L N M : ℕ} (A : ℕ → ℝ) : Sector L N M → ℂ :=
  fun η => (coordinate A η.val : ℂ)

private theorem coordinate_pos {L : ℕ} (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (η : Mode L → ℕ) : 0 < coordinate A η := by
  apply prod_pos
  intro a _
  exact div_pos (pow_pos (Real.sqrt_pos.mpr (hA _)) _)
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos (η a)))

private def bump {L : ℕ} (η : Mode L → ℕ) (i : Mode L) : Mode L → ℕ :=
  fun a => η a + if a = i then 1 else 0

private theorem coordinate_bump {L : ℕ} (A : ℕ → ℝ) (η : Mode L → ℕ) (i : Mode L) :
    Real.sqrt ((η i : ℝ) + 1) * coordinate A (bump η i) =
      Real.sqrt (A i.val) * coordinate A η := by
  let u := fun a : Mode L => Real.sqrt (A a.val) ^ η a / Real.sqrt (η a).factorial
  let v := fun a : Mode L =>
    Real.sqrt (A a.val) ^ bump η i a / Real.sqrt (bump η i a).factorial
  change _ * ∏ a, v a = _ * ∏ a, u a
  rw [← mul_prod_erase univ v (mem_univ i), ← mul_prod_erase univ u (mem_univ i)]
  have hprod : (∏ a ∈ univ.erase i, v a) = ∏ a ∈ univ.erase i, u a := by
    apply prod_congr rfl
    intro a ha
    simp [u, v, bump, ne_of_mem_erase ha]
  rw [hprod, ← mul_assoc, ← mul_assoc]
  congr 1
  have hs : 0 < Real.sqrt ((η i : ℝ) + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  simp only [u, v, bump, ite_true, eq_self, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (η i : ℝ) + 1)]
  have hf : 0 < Real.sqrt ((η i).factorial : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.factorial_pos (η i))
  field_simp [hs.ne', hf.ne']

/-- The coefficient in the source, with the entire pair product under the square root. -/
def pairWeight (A : ℕ → ℝ) (i j : ℕ) : ℝ := Real.sqrt (A i * A j)

private theorem pair_lowers_vector {L N M : ℕ} (hN : 2 ≤ N) (i j : Mode L)
    (hM : i.val + j.val ≤ M) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    pairAnnihilator hN i j hM *ᵥ occupationVector A =
      pairWeight A i.val j.val • occupationVector A := by
  classical
  funext ζ
  rw [Matrix.mulVec_apply_eq_sum, sum_eq_single (raise hN i j hM ζ)]
  · simp only [pairAnnihilator, ite_true, eq_self, occupationVector, Pi.smul_apply,
      Complex.real_smul, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have hraise : (raise hN i j hM ζ).val = bump (bump ζ.val j) i := by
      funext a
      simp only [raise, bump, increment]
      omega
    rw [hraise]
    have hq : pairCount (bump (bump ζ.val j) i) i j =
        ((bump ζ.val j i : ℝ) + 1) * ((ζ.val j : ℝ) + 1) := by
      by_cases hij : i = j
      · subst j
        simp [pairCount, bump, Nat.cast_add]
      · simp [pairCount, bump, hij, Ne.symm hij, Nat.cast_add]
    rw [hq, Real.sqrt_mul (by positivity), pairWeight, Real.sqrt_mul (hA _).le]
    calc
      _ = Real.sqrt ((ζ.val j : ℝ) + 1) *
          (Real.sqrt ((bump ζ.val j i : ℝ) + 1) * coordinate A (bump (bump ζ.val j) i)) := by ring
      _ = _ := by
        rw [coordinate_bump, ← mul_assoc, mul_comm (Real.sqrt ((ζ.val j : ℝ) + 1)),
          mul_assoc, coordinate_bump, ← mul_assoc]
  · intro η _ hη
    simp [pairAnnihilator, Ne.symm hη]
  · simp

private theorem occupationVector_ne_zero {L N M : ℕ} [Nonempty (Sector L N M)]
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) : (occupationVector A : Sector L N M → ℂ) ≠ 0 := by
  obtain ⟨η⟩ := ‹Nonempty (Sector L N M)›
  intro h
  have hz := congrFun h η
  exact (coordinate_pos A hA η.val).ne' (by simpa [occupationVector] using hz)

private def leftMode {M : ℕ} (j : Mode M) (k : Fin (j.val + 1)) : Mode M :=
  ⟨k.val, by omega⟩

private def rightMode {M : ℕ} (j : Mode M) (k : Fin (j.val + 1)) : Mode M :=
  ⟨j.val - k.val, by omega⟩

private theorem mode_sum {M : ℕ} (j : Mode M) (k : Fin (j.val + 1)) :
    (leftMode j k).val + (rightMode j k).val = j.val := by
  change k.val + (j.val - k.val) = j.val
  omega

private def pairAt {N M : ℕ} (hN : 2 ≤ N) (i l : Mode M)
    (j : ℕ) (hj : j ≤ M) (h : i.val + l.val = j) :
    Matrix (Sector M (N - 2) (M - j)) (Sector M N M) ℂ :=
  h ▸ pairAnnihilator hN i l (h.symm ▸ hj)

private theorem pairAt_adjoint_square {N M : ℕ} (hN : 2 ≤ N) (i l : Mode M)
    (j : ℕ) (hj : j ≤ M) (h : i.val + l.val = j) :
    (pairAt hN i l j hj h)ᴴ * pairAt hN i l j hj h =
      Matrix.diagonal (fun η => (pairCount η.val i l : ℂ)) := by
  subst j
  exact pair_adjoint_square hN i l hj

private theorem pairAt_lowers_vector {N M : ℕ} (hN : 2 ≤ N) (i l : Mode M)
    (j : ℕ) (hj : j ≤ M) (h : i.val + l.val = j) (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    pairAt hN i l j hj h *ᵥ occupationVector A =
      pairWeight A i.val l.val • occupationVector A := by
  subst j
  exact pair_lowers_vector hN i l hj A hA

private def blockPair {N M : ℕ} (hN : 2 ≤ N) (j : Mode M) (k : Fin (j.val + 1)) :
    Matrix (Sector M (N - 2) (M - j.val)) (Sector M N M) ℂ :=
  pairAt hN (leftMode j k) (rightMode j k) j.val (Nat.le_of_lt_succ j.isLt) (mode_sum j k)

private theorem sum_momentum_blocks {R : Type*} [AddCommMonoid R] {M : ℕ}
    (f : Mode M → Mode M → R) :
    (∑ j : Mode M, ∑ k : Fin (j.val + 1), f (leftMode j k) (rightMode j k)) =
      ∑ i : Mode M, ∑ l with i.val + l.val ≤ M, f i l := by
  classical
  rw [← Fintype.sum_sigma (fun a : (Σ j : Mode M, Fin (j.val + 1)) =>
    f (leftMode a.1 a.2) (rightMode a.1 a.2))]
  let valid := (univ : Finset (Mode M × Mode M)).filter (fun a => a.1.val + a.2.val ≤ M)
  calc
    _ = ∑ a ∈ valid, f a.1 a.2 := by
      apply sum_bij (fun a _ => (leftMode a.1 a.2, rightMode a.1 a.2))
      · intro a _
        simp only [valid, mem_filter, mem_univ, true_and, mode_sum]
        omega
      · intro a _ b _ h
        have hleft := congrArg (fun p : Mode M × Mode M => p.1.val) h
        have hsum := congrArg (fun p : Mode M × Mode M => p.1.val + p.2.val) h
        simp only [mode_sum] at hsum
        have he : a.1 = b.1 := Fin.ext hsum
        obtain ⟨j, k⟩ := a
        obtain ⟨l, m⟩ := b
        change j = l at he
        subst l
        cases (Fin.ext hleft : k = m)
        rfl
      · rintro ⟨i, l⟩ ha
        have hv : i.val + l.val ≤ M := (mem_filter.mp ha).2
        let j : Mode M := ⟨i.val + l.val, by omega⟩
        let k : Fin (j.val + 1) := ⟨i.val, by dsimp [j]; omega⟩
        exact ⟨⟨j, k⟩, mem_univ _, Prod.ext (Fin.ext rfl) (Fin.ext (Nat.add_sub_cancel_left _ _))⟩
      · intro a _
        rfl
    _ = _ := by
      simp only [valid, sum_filter, Fintype.sum_prod_type]

private def blockWeight {M : ℕ} (A : ℕ → ℝ) (j : Mode M) (k : Fin (j.val + 1)) : ℝ :=
  pairWeight A (leftMode j k).val (rightMode j k).val

private def pairBlock {N M : ℕ} (hN : 2 ≤ N) (A : ℕ → ℝ) (j : Mode M) :
    Matrix (Sector M (N - 2) (M - j.val)) (Sector M N M) ℂ :=
  ∑ k, blockWeight A j k • blockPair hN j k

/-- The ordered four-operator sum with mode weights `A` and block coefficients `c`. -/
def weightedHamiltonian (A c : ℕ → ℝ) (N M : ℕ) : Matrix (Sector M N M) (Sector M N M) ℂ :=
  if hN : 2 ≤ N then
    ∑ j : Mode M, (c j.val / 2) • ∑ k, ∑ l,
      (blockWeight A j k * blockWeight A j l) • ((blockPair hN j k)ᴴ * blockPair hN j l)
  else 0

private theorem weightedHamiltonian_eq_blocks (A c : ℕ → ℝ) (N M : ℕ) :
    weightedHamiltonian A c N M =
      if hN : 2 ≤ N then
        ∑ j : Mode M, (c j.val / 2) • ((pairBlock hN A j)ᴴ * pairBlock hN A j)
      else 0 := by
  unfold weightedHamiltonian
  split
  · apply sum_congr rfl
    intro j _
    congr 1
    rw [pairBlock, Matrix.conjTranspose_sum, Matrix.sum_mul]
    simp_rw [Matrix.mul_sum, Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  · rfl

/-- The claimed top eigenvalue, with real subtraction even for the vacuum. -/
def energy (σ : ℝ) (N M : ℕ) : ℝ := ((N : ℝ) - 1) * (N + 2 * σ * M) / 2

private theorem scalar_diagonal {N M : ℕ} (hN : 2 ≤ N) (σ : ℝ) :
    (∑ j : Mode M, ((1 + σ * j.val) / 2) •
      ∑ k, (blockPair hN j k)ᴴ * blockPair hN j k) =
      energy σ N M • (1 : Matrix (Sector M N M) (Sector M N M) ℂ) := by
  classical
  simp_rw [blockPair, pairAt_adjoint_square]
  ext η ξ
  by_cases h : η = ξ
  · subst ξ
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Complex.real_smul, mul_one, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    apply congrArg Complex.ofReal
    let f (i l : Mode M) : ℝ :=
      (1 + σ * ((i.val + l.val : ℕ) : ℝ)) * pairCount η.val i l
    calc
      _ = (∑ j : Mode M, ∑ k, f (leftMode j k) (rightMode j k)) / 2 := by
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro j _
        rw [mul_sum, Finset.sum_div]
        apply sum_congr rfl
        intro k _
        unfold f
        rw [mode_sum, div_mul_eq_mul_div]
      _ = _ := by
        rw [sum_momentum_blocks]
        exact occupation_diagonal_sum Fin.val η.val N M η.property.1 η.property.2 σ
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private def pairDefect {N M : ℕ} (hN : 2 ≤ N) (A : ℕ → ℝ) (j : Mode M)
    (k l : Fin (j.val + 1)) : Matrix (Sector M (N - 2) (M - j.val)) (Sector M N M) ℂ :=
  blockWeight A j k • blockPair hN j l - blockWeight A j l • blockPair hN j k

private def defect {N M : ℕ} (hN : 2 ≤ N) (A c : ℕ → ℝ) :
    Matrix (Sector M N M) (Sector M N M) ℂ :=
  ∑ j : Mode M, (c j.val / 4) • ∑ k, ∑ l, (pairDefect hN A j k l)ᴴ * pairDefect hN A j k l

private theorem weighted_factorization {N M : ℕ} (hN : 2 ≤ N) (σ : ℝ) (A c : ℕ → ℝ)
    (hc : ∀ j, c j * ∑ k : Fin (j + 1), pairWeight A k.val (j - k.val) ^ 2 = 1 + σ * j) :
    energy σ N M • (1 : Matrix (Sector M N M) (Sector M N M) ℂ) =
      weightedHamiltonian A c N M + defect hN A c := by
  rw [← scalar_diagonal hN, weightedHamiltonian_eq_blocks, dite_eq_left hN, defect, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  have hg := weighted_gram_defect univ (blockWeight A j) (blockPair hN j)
  change (∑ k, ∑ l, (pairDefect hN A j k l)ᴴ * pairDefect hN A j k l) =
    2 • ((∑ k, blockWeight A j k ^ 2) • (∑ k, (blockPair hN j k)ᴴ * blockPair hN j k) -
      (pairBlock hN A j)ᴴ * pairBlock hN A j) at hg
  rw [hg, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_sub, smul_smul]
  norm_num
  have hj : c j.val * (∑ k, blockWeight A j k ^ 2) = 1 + σ * j.val := hc j.val
  have hcoeff : c j.val / 4 * 2 * (∑ k, blockWeight A j k ^ 2) = (1 + σ * j.val) / 2 := by
    linarith only [hj]
  rw [hcoeff]
  module

private theorem defect_posSemidef {N M : ℕ} (hN : 2 ≤ N) (A c : ℕ → ℝ)
    (hc : ∀ j, 0 ≤ c j) : (defect (M := M) hN A c).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro j _
  apply Matrix.PosSemidef.smul _ (div_nonneg (hc _) (by norm_num))
  exact Matrix.posSemidef_sum _ fun k _ =>
    Matrix.posSemidef_sum _ fun l _ => Matrix.posSemidef_conjTranspose_mul_self _

private theorem hamiltonian_posSemidef (A c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (N M : ℕ) :
    (weightedHamiltonian A c N M).PosSemidef := by
  rw [weightedHamiltonian_eq_blocks]
  split
  · exact Matrix.posSemidef_sum _ fun j _ =>
      (Matrix.posSemidef_conjTranspose_mul_self _).smul (div_nonneg (hc _) (by norm_num))
  · exact Matrix.PosSemidef.zero

private theorem defect_mulVec {N M : ℕ} (hN : 2 ≤ N) (A c : ℕ → ℝ) (hA : ∀ n, 0 < A n) :
    defect (M := M) hN A c *ᵥ occupationVector A = 0 := by
  have hzero (j : Mode M) (k l : Fin (j.val + 1)) :
      pairDefect hN A j k l *ᵥ occupationVector A = 0 := by
    simp only [pairDefect, Matrix.sub_mulVec, Matrix.smul_mulVec, blockPair,
      pairAt_lowers_vector _ _ _ _ _ _ _ hA, blockWeight, smul_smul]
    rw [mul_comm (pairWeight A _ _), sub_self]
  simp only [defect, Matrix.sum_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hzero,
    Matrix.mulVec_zero, sum_const_zero, smul_zero]

private theorem mem_spectrum_of_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (E : ℝ) (v : ι → ℂ) (hv : v ≠ 0) (he : H *ᵥ v = E • v) :
    E ∈ spectrum ℝ H := by
  rw [← spectrum.algebraMap_mem_iff ℂ]
  rw [← Matrix.spectrum_toLin']
  apply Module.End.HasEigenvalue.mem_spectrum
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
  change H *ᵥ v = (E : ℂ) • v
  exact he

private theorem le_energy_of_defect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H D : Matrix ι ι ℂ) (E : ℝ) (hH : H.IsHermitian) (hD : D.PosSemidef)
    (h : E • (1 : Matrix ι ι ℂ) = H + D) (x : ℝ) (hx : x ∈ spectrum ℝ H) : x ≤ E := by
  obtain ⟨i, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
  let u := hH.eigenvectorBasis i
  have hDu : D *ᵥ ⇑u = (E - hH.eigenvalues i) • ⇑u := by
    rw [← sub_eq_of_eq_add' h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hH.mulVec_eigenvectorBasis, sub_smul]
  have hp := (RCLike.nonneg_iff.mp (hD.dotProduct_mulVec_nonneg (⇑u))).1
  rw [hDu, dotProduct_smul, RCLike.smul_re, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hH.eigenvectorBasis.orthonormal.1 i] at hp
  simpa using hp

private theorem weighted_spectrum (σ : ℝ) (A c : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hc : ∀ j, 0 ≤ c j)
    (hw : ∀ j, c j * ∑ k : Fin (j + 1), pairWeight A k.val (j - k.val) ^ 2 = 1 + σ * j)
    (N M : ℕ) [Nonempty (Sector M N M)] :
    (weightedHamiltonian A c N M).IsHermitian ∧
      IsGreatest (spectrum ℝ (weightedHamiltonian A c N M)) (energy σ N M) ∧
      (occupationVector A : Sector M N M → ℂ) ≠ 0 ∧
      weightedHamiltonian A c N M *ᵥ occupationVector A = energy σ N M • occupationVector A := by
  have hH := (hamiltonian_posSemidef A c hc N M).isHermitian
  have hv : (occupationVector A : Sector M N M → ℂ) ≠ 0 := occupationVector_ne_zero A hA
  refine ⟨hH, ?_⟩
  by_cases hN : 2 ≤ N
  · have hfactor := weighted_factorization (M := M) hN σ A c hw
    have he := congrArg (fun H : Matrix (Sector M N M) (Sector M N M) ℂ =>
      H *ᵥ occupationVector A) hfactor
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      defect_mulVec (M := M) hN A c hA, add_zero] at he
    exact ⟨⟨mem_spectrum_of_vector _ _ _ hv he.symm,
      fun x hx => le_energy_of_defect _ _ _ hH (defect_posSemidef hN A c hc) hfactor x hx⟩,
      hv, he.symm⟩
  · have hE : energy σ N M = 0 := by
      have hn : N = 0 ∨ N = 1 := by omega
      rcases hn with rfl | rfl
      · obtain ⟨η⟩ := ‹Nonempty (Sector M 0 M)›
        have hz : ∀ a, η.val a = 0 := by
          intro a
          have hle : η.val a ≤ ∑ b, η.val b :=
            single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)
          rw [η.property.1] at hle
          omega
        have hM : M = 0 := by simpa only [hz, mul_zero, sum_const_zero] using η.property.2.symm
        simp [energy, hM]
      · simp [energy]
    have hh : weightedHamiltonian A c N M = 0 := by simp [weightedHamiltonian, hN]
    have he : weightedHamiltonian A c N M *ᵥ occupationVector A =
        energy σ N M • occupationVector A := by simp [hh, hE]
    have hD : (0 : Matrix (Sector M N M) (Sector M N M) ℂ).PosSemidef := .zero
    exact ⟨⟨mem_spectrum_of_vector _ _ _ hv he,
      fun x hx => le_energy_of_defect _ _ _ hH hD (by simp [hh, hE]) x hx⟩, hv, he⟩

open PowerSeries

/-- Evnin's real Raney coefficients from Eq. (31). -/
def raney (σ r : ℝ) (j : ℕ) : ℝ :=
  r * Real.Gamma (σ * j + r) /
    (Real.Gamma ((σ - 1) * j + r + 1) * Real.Gamma ((j : ℝ) + 1))

/-- The prefactor of the squared block in Evnin's Eq. (32). -/
def blockCoefficient (σ : ℝ) (j : ℕ) : ℝ :=
  (1 + j * (σ - 1) / 2) / raney σ 1 j

private theorem raney_pos (σ r : ℝ) (hσ : 1 ≤ σ) (hr : 0 < r) (j : ℕ) :
    0 < raney σ r j := by
  have h : 0 ≤ σ - 1 := sub_nonneg.mpr hσ
  have hs : 0 ≤ σ := by linarith
  unfold raney
  exact div_pos (mul_pos hr (Real.Gamma_pos_of_pos (by positivity)))
    (mul_pos (Real.Gamma_pos_of_pos (by positivity)) (Real.Gamma_pos_of_pos (by positivity)))

private theorem raney_zero (σ r : ℝ) (hr : 0 < r) : raney σ r 0 = 1 := by
  simp [raney, Real.Gamma_add_one hr.ne', (mul_pos hr (Real.Gamma_pos_of_pos hr)).ne']

private theorem gamma_asc (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * (ascPochhammer ℝ n).eval x := by
  induction n with
  | zero => simp [ascPochhammer_zero]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity), ih,
      ascPochhammer_succ_eval]
    ring

private theorem raney_choose (σ r : ℝ) (hσ : 1 ≤ σ) (hr : 0 < r) (n : ℕ) :
    ((n : ℝ) + 1) * raney σ r (n + 1) =
      r * Ring.choose (r - 1 + σ * (n + 1 : ℕ)) n := by
  let x : ℝ := (σ - 1) * (n + 1 : ℕ) + r + 1
  have hx : 0 < x := by
    have h : 0 ≤ σ - 1 := sub_nonneg.mpr hσ
    dsimp [x]
    positivity
  have he : σ * (n + 1 : ℕ) + r = x + n := by simp [x, Nat.cast_add]; ring
  have hchoose : (n.factorial : ℝ) * Ring.choose (r - 1 + σ * (n + 1 : ℕ)) n =
      (ascPochhammer ℝ n).eval x := by
    rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose,
      Polynomial.descPochhammer_smeval_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
    congr 1
    simp [x, Nat.cast_add]
    ring
  have hden : (σ - 1) * (n + 1 : ℕ) + r + 1 = x := rfl
  rw [raney, he, hden, gamma_asc x hx, Real.Gamma_nat_eq_factorial, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, ← hchoose]
  field_simp [(Real.Gamma_pos_of_pos hx).ne',
    (show (n.factorial : ℝ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero n)]
  push_cast
  congr 1
  ring

private theorem binomialSeries_pow_real (σ : ℝ) (n : ℕ) :
    binomialSeries ℝ σ ^ n = binomialSeries ℝ (σ * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← binomialSeries_add, Nat.cast_succ, mul_add, mul_one]

private theorem raney_convolution (σ : ℝ) (hσ : 1 ≤ σ) (j : ℕ) :
    (∑ k : Fin (j + 1), raney σ 1 k.val * raney σ 1 (j - k.val)) = raney σ 2 j := by
  let F := binomialSeries ℝ σ
  let G := binomialSeries ℝ (-σ)
  have hg : G * F = 1 := by
    dsimp [G, F]
    rw [← binomialSeries_add, neg_add_cancel, binomialSeries_zero]
  let P := (X : PowerSeries ℝ) * G
  have hp : constantCoeff P = 0 := by simp [P]
  have hp₁ : IsUnit (coeff 1 P) := by simp [P, G, coeff_succ_X_mul]
  let T := P.substInvOfIsUnit hp₁
  have ht : constantCoeff T = 0 := constantCoeff_substInvOfIsUnit P hp₁
  have hsubst : HasSubst T := HasSubst.of_constantCoeff_zero ht
  have hinv : T * G.subst T = X := by
    have h := subst_substInvOfIsUnit_right P hp hp₁
    change P.subst T = X at h
    simpa only [P, subst_mul hsubst, subst_X hsubst] using h
  have hfix : T = X * F.subst T := by
    rw [← hinv, mul_assoc, ← subst_mul hsubst, hg]
    have hone : (1 : PowerSeries ℝ).subst T = 1 := by
      rw [← coe_substAlgHom (R := ℝ) hsubst]
      exact (substAlgHom (R := ℝ) hsubst).map_one
    rw [hone, mul_one]
  let coeffSeries := fun r : ℝ => (binomialSeries ℝ r).subst T
  have hC (r : ℕ) (hr : 0 < r) (n : ℕ) : coeff n (coeffSeries r) = raney σ r n := by
    cases n with
    | zero =>
      unfold coeffSeries
      rw [coeff_zero_eq_constantCoeff_apply]
      change MvPowerSeries.constantCoeff ((binomialSeries ℝ (r : ℝ)).subst T) = _
      rw [constantCoeff_subst_of_constantCoeff_zero ht,
        binomialSeries_constantCoeff, map_one, raney_zero σ r (by exact_mod_cast hr)]
    | succ n =>
      have hd : derivative (R := ℝ) (binomialSeries ℝ (r : ℝ)) =
          (r : ℝ) • binomialSeries ℝ ((r - 1 : ℕ) : ℝ) := by
        rw [binomialSeries_nat, binomialSeries_nat, derivative_pow]
        simp [smul_eq_C_mul, mul_comm]
      have h := D5.S3.Combinatorics.WeightedBond.lagrange_burmann T
        (binomialSeries ℝ (r : ℝ)) F ht hfix n
      rw [hd, smul_mul_assoc, binomialSeries_pow_real, ← binomialSeries_add] at h
      have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) (Nat.one_le_iff_ne_zero.mpr hr.ne'))
      rw [hcast] at h
      simp only [map_smul, binomialSeries_coeff, smul_eq_mul, mul_one] at h
      have hc := raney_choose σ r hσ (by exact_mod_cast hr) n
      change coeff (n + 1) (coeffSeries r) = raney σ r (n + 1)
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact mul_left_cancel₀ hpos.ne' (h.trans hc.symm)
  have hm : coeffSeries 2 = coeffSeries 1 * coeffSeries 1 := by
    unfold coeffSeries
    rw [show (2 : ℝ) = 1 + 1 by norm_num, binomialSeries_add, subst_mul hsubst]
  have hc := congrArg (coeff j) hm
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l =>
    coeff k (coeffSeries 1) * coeff l (coeffSeries 1))] at hc
  have h1 (n : ℕ) : coeff n (coeffSeries 1) = raney σ 1 n := by simpa using hC 1 (by decide) n
  have h2 (n : ℕ) : coeff n (coeffSeries 2) = raney σ 2 n := by simpa using hC 2 (by decide) n
  simp only [h1, h2] at hc
  rw [Fin.sum_univ_eq_sum_range (fun k => raney σ 1 k * raney σ 1 (j - k))]
  exact hc.symm

private theorem raney_ratio (σ : ℝ) (hσ : 1 ≤ σ) (j : ℕ) :
    blockCoefficient σ j * raney σ 2 j = 1 + σ * j := by
  let x : ℝ := σ * j + 1
  let y : ℝ := (σ - 1) * j + 2
  have hs : 0 ≤ σ := by linarith
  have hs' : 0 ≤ σ - 1 := sub_nonneg.mpr hσ
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hf : 0 < Real.Gamma ((j : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have ha (r : ℝ) : raney σ r j =
      r * Real.Gamma (x + (r - 1)) /
        (Real.Gamma (y + (r - 1)) * Real.Gamma ((j : ℝ) + 1)) := by
    unfold raney
    congr 2 <;> dsimp [x, y] <;> ring
  rw [blockCoefficient, ha 1, ha 2]
  norm_num only [sub_self, add_zero, show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
  rw [Real.Gamma_add_one hx.ne', Real.Gamma_add_one hy.ne']
  have hy' : y ≠ 0 := hy.ne'
  field_simp [hy', (Real.Gamma_pos_of_pos hx).ne', (Real.Gamma_pos_of_pos hy).ne', hf.ne']
  dsimp [x, y]
  ring

private theorem source_weight_identity (σ : ℝ) (hσ : 1 ≤ σ) (j : ℕ) :
    blockCoefficient σ j *
      (∑ k : Fin (j + 1), pairWeight (raney σ 1) k.val (j - k.val) ^ 2) = 1 + σ * j := by
  have hpos := raney_pos σ 1 hσ (by norm_num)
  simp only [pairWeight, Real.sq_sqrt (mul_nonneg (hpos _).le (hpos _).le)]
  rw [raney_convolution σ hσ, raney_ratio σ hσ]

/-- Evnin's normally ordered Hamiltonian (Eqs. (19), (30)–(32)). -/
def hamiltonian (σ : ℝ) (N M : ℕ) : Matrix (Sector M N M) (Sector M N M) ℂ :=
  weightedHamiltonian (raney σ 1) (blockCoefficient σ) N M

/-- Evnin's conjectured top eigenvalue together with its explicit vector. -/
def claim : Prop :=
  ∀ (σ : ℝ), 1 ≤ σ → ∀ (N M : ℕ), ∀ [Nonempty (Sector M N M)],
    (hamiltonian σ N M).IsHermitian ∧
      IsGreatest (spectrum ℝ (hamiltonian σ N M)) (energy σ N M) ∧
      (occupationVector (raney σ 1) : Sector M N M → ℂ) ≠ 0 ∧
      hamiltonian σ N M *ᵥ occupationVector (raney σ 1) =
        energy σ N M • occupationVector (raney σ 1)

/-- The exact top eigenvalue of Evnin's Hamiltonian, attained by the factorial vector. -/
theorem top_finite_sector_eigenvalue : claim := by
  intro σ hσ N M hsector
  have hpos := raney_pos σ 1 hσ (by norm_num)
  have hc (j : ℕ) : 0 ≤ blockCoefficient σ j := by
    have h : 0 ≤ σ - 1 := sub_nonneg.mpr hσ
    unfold blockCoefficient
    exact div_nonneg (by positivity) (hpos j).le
  exact weighted_spectrum σ (raney σ 1) (blockCoefficient σ) hpos hc
    (source_weight_identity σ hσ) N M

end
end D5.S3.Quantum.FockSpace.EvninQuantumSector
