/- GID: D5/S1/Eigenstructure/NilpotentDimensionThree
   generality: G
   mirror-B: D5/B/S1/Eigenstructure/NilpotentDimensionThree
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: The two nonzero nilpotent normal forms in dimension three over any field. -/

import D5.S1.Eigenstructure.NilpotentJordanChains
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases

namespace D5.S1.Eigenstructure.NilpotentDimensionThree

open Module
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem basis_from_three_indices {ι : Type*} (basis : Basis ι K V)
    (hdim : finrank K V = 3) (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ B : Basis (Fin 3) K V, B 0 = basis a ∧ B 1 = basis b ∧ B 2 = basis c := by
  let indices : Fin 3 → ι := ![a, b, c]
  have hinj : Function.Injective indices := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [indices]
  have hind := basis.linearIndependent.comp indices hinj
  let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp [hdim])
  exact ⟨B, by simp [B, indices]⟩

private theorem exists_chain_longer {ι : Type*} [Fintype ι] (s : ι → ℕ+)
    (f : Module.End K V) (m : ℕ)
    (hrank : finrank K (LinearMap.range (f ^ m)) = ∑ i, ((s i : ℕ) - m))
    (hpow : f ^ m ≠ 0) : ∃ i : ι, m < (s i : ℕ) := by
  classical
  by_contra! h
  have hzero : finrank K (LinearMap.range (f ^ m)) = 0 := by
    rw [hrank]
    simp [Nat.sub_eq_zero_of_le (h _)]
  exact hpow (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero))

/-- In dimension three, a nonzero operator with cube zero has an ordered
basis for the shift with one nonzero entry or the shift with two. The
square of the operator distinguishes the two alternatives. -/
theorem exists_basis (f : Module.End K V) (hdim : finrank K V = 3)
    (hne : f ≠ 0) (hcube : f ^ 3 = 0) :
    ∃ b : Basis (Fin 3) K V, f (b 0) = 0 ∧ f (b 1) = b 0 ∧
      ((f ^ 2 = 0 ∧ f (b 2) = 0) ∨ (f ^ 2 ≠ 0 ∧ f (b 2) = b 1)) := by
  classical
  obtain ⟨ι, hι, s, basis, hchain, hrank⟩ :=
    NilpotentJordanChains.nilpotent_jordan_chains_rank f ⟨3, hcube⟩
  letI := hι
  have hstep (i : ι) (j : ℕ) (hj : j + 1 < (s i : ℕ)) :
      f (basis ⟨i, ⟨j, by omega⟩⟩) = basis ⟨i, ⟨j + 1, hj⟩⟩ := by
    simpa [hj] using hchain 1 i ⟨j, by omega⟩
  have hlast (i : ι) (j : ℕ) (hj : j < (s i : ℕ)) (he : (s i : ℕ) ≤ j + 1) :
      f (basis ⟨i, ⟨j, hj⟩⟩) = 0 := by
    simpa [not_lt.mpr he] using hchain 1 i ⟨j, hj⟩
  by_cases hsquare : f ^ 2 = 0
  · obtain ⟨i, hi⟩ := exists_chain_longer s f 1 (hrank 1) (by simpa using hne)
    have hsize : (s i : ℕ) = 2 := by
      by_contra! h
      have hi₂ : 2 < (s i : ℕ) := by omega
      have hzero : basis ⟨i, ⟨2, hi₂⟩⟩ = 0 := by
        simpa [hi₂, hsquare] using (hchain 2 i ⟨0, by omega⟩).symm
      exact basis.ne_zero _ hzero
    have htotal : (∑ i, (s i : ℕ)) = 3 := by
      simpa [hdim, Fintype.card_sigma] using (finrank_eq_card_basis basis).symm
    obtain ⟨k, hk⟩ : ∃ k, k ≠ i := by
      by_contra! h
      have heq : (∑ j, (s j : ℕ)) = s i := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          exact (hji (h j)).elim
        · simp
      omega
    have hpair : (s i : ℕ) + s k ≤ ∑ j, (s j : ℕ) := by
      calc
        _ = ∑ j ∈ ({i, k} : Finset ι), (s j : ℕ) := by simp [Ne.symm hk]
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hk0 : 0 < (s k : ℕ) := (s k).prop
    have hksize : (s k : ℕ) = 1 := by omega
    let a : Σ j : ι, Fin (s j) := ⟨i, ⟨1, hi⟩⟩
    let b : Σ j : ι, Fin (s j) := ⟨i, ⟨0, by omega⟩⟩
    let c : Σ j : ι, Fin (s j) := ⟨k, ⟨0, hk0⟩⟩
    obtain ⟨B, hA, hB, hC⟩ := basis_from_three_indices basis hdim a b c
      (by intro h; have := congrArg (fun x : Σ j : ι, Fin (s j) => x.2.val) h; simp [a, b] at this)
      (by intro h; exact hk (congrArg Sigma.fst h).symm)
      (by intro h; exact hk (congrArg Sigma.fst h).symm)
    refine ⟨B, ?_, ?_, Or.inl ⟨hsquare, ?_⟩⟩
    · rw [hA]
      exact hlast i 1 hi (by omega)
    · rw [hB, hA]
      exact hstep i 0 hi
    · rw [hC]
      exact hlast k 0 hk0 (by omega)
  · obtain ⟨i, hi⟩ := exists_chain_longer s f 2 (hrank 2) hsquare
    have hsize : (s i : ℕ) ≤ 3 := by
      by_contra! h
      have hzero : basis ⟨i, ⟨3, h⟩⟩ = 0 := by
        simpa [h, hcube] using (hchain 3 i ⟨0, by omega⟩).symm
      exact basis.ne_zero _ hzero
    let a : Σ j : ι, Fin (s j) := ⟨i, ⟨2, hi⟩⟩
    let b : Σ j : ι, Fin (s j) := ⟨i, ⟨1, by omega⟩⟩
    let c : Σ j : ι, Fin (s j) := ⟨i, ⟨0, by omega⟩⟩
    obtain ⟨B, hA, hB, hC⟩ := basis_from_three_indices basis hdim a b c
      (by intro h; have := congrArg (fun x : Σ j : ι, Fin (s j) => x.2.val) h; simp [a, b] at this)
      (by intro h; have := congrArg (fun x : Σ j : ι, Fin (s j) => x.2.val) h; simp [a, c] at this)
      (by intro h; have := congrArg (fun x : Σ j : ι, Fin (s j) => x.2.val) h; simp [b, c] at this)
    refine ⟨B, ?_, ?_, Or.inr ⟨hsquare, ?_⟩⟩
    · rw [hA]
      exact hlast i 2 hi hsize
    · rw [hB, hA]
      exact hstep i 1 hi
    · rw [hC, hB]
      exact hstep i 0 (by omega)

end D5.S1.Eigenstructure.NilpotentDimensionThree
