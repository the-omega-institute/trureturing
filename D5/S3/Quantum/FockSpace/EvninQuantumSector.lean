/- GID: D5/S3/Quantum/FockSpace/EvninQuantumSector
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/EvninQuantumSector
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted normal-ordered Hamiltonian in Evnin's finite occupation sectors. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

compile_only_with_mathlib

/-! The normalized occupation model for Evnin, arXiv:2607.25445v3, §2.3. -/

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
    · have hξ : raise hN i j hM ζ ≠ ξ := fun h => he (hζ.symm.trans h)
      simp [Matrix.conjTranspose_apply, pairAnnihilator, hζ, hξ]
    · simp [Matrix.conjTranspose_apply, pairAnnihilator, hζ]

end
end D5.S3.Quantum.FockSpace.EvninQuantumSector
