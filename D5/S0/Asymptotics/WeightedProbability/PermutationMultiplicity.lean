/- GID: D5/S0/Asymptotics/WeightedProbability/PermutationMultiplicity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/WeightedProbability/PermutationMultiplicity
   mirror-E: none(waiver:general-permutation-normalization)
   anchors: []
   utility: none
   digest: Full permutation partitions retain fixed-point multiplicities in the centralizer factor. -/

import Mathlib.GroupTheory.Perm.Centralizer

/-
The multiplicity normalization is adapted from Tau Ceti, released under
Apache 2.0; the complete license is in Library/notes/tauceti2026classsizes.md.
It is the original normalization used by DistinctCycleSizeLimit, with the
finite carrier generalized. The classical class-size formula is due to Cauchy.
-/

open scoped BigOperators
open Finset

namespace D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity

noncomputable section

def z : Multiset ℕ → ℕ := fun m =>
  ∏ i ∈ m.toFinset, i ^ m.count i * (m.count i).factorial
theorem hz_prod : ∀ (m : Multiset ℕ) (s : Finset ℕ), m.toFinset ⊆ s →
    z m = ∏ i ∈ s, i ^ m.count i * (m.count i).factorial := by
  intro m s hs
  refine Finset.prod_subset hs ?_
  intro i _ hi
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hi)]
  simp
theorem hz_perm : ∀ {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α),
    z σ.partition.parts =
      (Fintype.card α - σ.cycleType.sum).factorial * σ.cycleType.prod *
        ∏ i ∈ σ.cycleType.toFinset, (σ.cycleType.count i).factorial := by
  intro α _ _ σ
  let m := σ.cycleType
  let k := Fintype.card α - σ.support.card
  have hparts : σ.partition.parts = m + Multiset.replicate k 1 := by
    simp only [Equiv.Perm.parts_partition, m, k]
  have h1 : (1 : ℕ) ∉ m := fun h => by
    simpa using Equiv.Perm.two_le_of_mem_cycleType h
  have hsub : σ.partition.parts.toFinset ⊆ insert 1 m.toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, hparts, Multiset.mem_add] at hi
    rcases hi with h | h
    · exact Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr h)
    · exact Finset.mem_insert.mpr (Or.inl (Multiset.eq_of_mem_replicate h))
  have hcount : ∀ i ∈ m.toFinset, σ.partition.parts.count i = m.count i := by
    intro i hi
    have hne : (1 : ℕ) ≠ i := fun h => h1 (h ▸ Multiset.mem_toFinset.mp hi)
    rw [hparts, Multiset.count_add, Multiset.count_replicate, if_neg hne, add_zero]
  have hcount_one : σ.partition.parts.count 1 = k := by
    rw [hparts, Multiset.count_add, Multiset.count_eq_zero_of_notMem h1,
      Multiset.count_replicate_self, zero_add]
  rw [hz_prod _ _ hsub, Finset.prod_insert (by simpa using h1), hcount_one,
    Finset.prod_congr rfl (fun i hi => by rw [hcount i hi]), Finset.prod_mul_distrib,
    ← Finset.prod_multiset_count, one_pow, one_mul]
  dsimp [m, k]
  rw [Equiv.Perm.sum_cycleType]
  ring

end

end D5.S0.Asymptotics.WeightedProbability.PermutationMultiplicity
