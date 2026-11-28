/- GID: D5/S3/Quantum/FockSpace/EvninQuantumSector
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/EvninQuantumSector
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted normal-ordered Hamiltonian in Evnin's finite occupation sectors. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The normalized occupation model for Evnin, arXiv:2607.25445v3, §2.3. -/

compile_only_with_mathlib

set_option autoImplicit false
open scoped BigOperators Matrix
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
  <;> ring

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

end
end D5.S3.Quantum.FockSpace.EvninQuantumSector
