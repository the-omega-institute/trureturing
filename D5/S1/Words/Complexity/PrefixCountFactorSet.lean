/- GID: D5/S1/Words/Complexity/PrefixCountFactorSet
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PrefixCountFactorSet
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Prefix growth on a word subshift equals its base factor complexity. -/

import D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
import D5.S1.Words.Complexity.SubshiftTopology

namespace D5.S1.Words.Complexity.PrefixCountFactorSet

open D5.S1.Dynamics.Symbolic.PrefixGrowthEntropy
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open Set SymbolicDynamics

noncomputable section

variable {A : Type*} [Fintype A] [Nonempty A] [Nontrivial A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [TopologicalSpace A]
  [DiscreteTopology A]

private theorem shift_mem_wordSubshift (x : ℕ → A) (i : ℕ) :
    FullShift.shift i x ∈ wordSubshift x := by
  induction i with
  | zero => simpa using self_mem_wordSubshift x
  | succ i ih =>
      have hshift : FullShift.shift (Nat.succ i) x =
          fun j ↦ FullShift.shift i x (j + 1) := by
        funext j
        simp only [FullShift.shift_apply]
        congr 1
        omega
      rw [hshift]
      exact wordSubshift_shift_invariant x ih

/-- Every prefix occurring in the word subshift is a factor of its base word,
and every base factor is realized by the corresponding shifted point. -/
theorem prefixCount_wordSubshift_eq_factorSet_card (x : ℕ → A) (n : ℕ) :
    prefixCount (wordSubshift x) n = (wordFactorSet x n).card := by
  classical
  have hset :
      Set.range (fun y : wordSubshift x => fun i : Fin n => (y : ℕ → A) i.val) =
        (wordFactorSet x n : Set (Fin n → A)) := by
    ext u
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property n
    · intro hu
      obtain ⟨i, hi⟩ := mem_wordFactorSet.mp hu
      refine ⟨⟨FullShift.shift i x, shift_mem_wordSubshift x i⟩, ?_⟩
      funext k
      simp only [FullShift.shift_apply, wordFactor] at hi ⊢
      exact (congrFun hi k).symm
  rw [show prefixCount (wordSubshift x) n =
      Nat.card (Set.range (fun y : wordSubshift x =>
        fun i : Fin n => (y : ℕ → A) i.val)) by rfl, hset]
  simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset]

end
end D5.S1.Words.Complexity.PrefixCountFactorSet

#print axioms D5.S1.Words.Complexity.PrefixCountFactorSet.prefixCount_wordSubshift_eq_factorSet_card
