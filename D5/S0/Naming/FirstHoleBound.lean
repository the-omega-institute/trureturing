/- GID: D5/S0/Naming/FirstHoleBound
   generality: G
   mirror-B: D5/B/S0/Naming/FirstHoleBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For a finite support S ⊆ ℕ with budget m = |S|, the first hole γ(S) = min(ℕ ∖ S) never exceeds the budget: γ(S) ≤ |S|, with equality exactly when S is the prefix (initial segment) {0,…,|S|−1} = Finset.range |S|. Proof by pigeonhole on Nat.find: range (|S|+1) ⊆ S would force |S|+1 ≤ |S|; the equality case pins range |S| ⊆ S and closes with eq_of_subset_of_card_le. Only this combinatorial first-hole characterization is recorded (定理 6.4(b) core); the measure clause μ(G(t)) = n^{−|S|} and the metric diameter formula diam G(t) = 2^{−γ(S)} — of which "prefix names uniquely minimize diameter" is the interpretation — are not covered. -/

import Mathlib

namespace D5.S0.Naming.FirstHoleBound

open Finset

/-- The **first hole** of a finite support `S ⊆ ℕ`: the least natural number *not* in `S`,
`γ(S) = min(ℕ ∖ S)`. In the naming picture it is the first unnamed / untested coordinate. -/
def firstHole (S : Finset ℕ) : ℕ := Nat.find (Infinite.exists_notMem_finset S)

/-- The first hole of an initial segment `{0, …, c-1}` is exactly `c`. -/
theorem firstHole_range (c : ℕ) : firstHole (Finset.range c) = c := by
  rw [firstHole, Nat.find_eq_iff]
  refine ⟨by simp [Finset.mem_range], ?_⟩
  intro m hm
  exact not_not.mpr (Finset.mem_range.mpr hm)

/-- **Budget-misalignment characterization (定理 6.4(b), combinatorial core).** For a finite support
`S ⊆ ℕ` with budget `m = |S|`, the first hole `γ(S) = min(ℕ ∖ S)` never exceeds the budget, and
equals it exactly when `S` is the prefix (initial segment) `{0, …, m-1} = Finset.range m`:
`firstHole S ≤ S.card ∧ (firstHole S = S.card ↔ S = Finset.range S.card)`.

No nonemptiness hypothesis is needed — the empty table `S = ∅` gives `firstHole ∅ = 0 = |∅|` with
`∅ = Finset.range 0`. The bound is by pigeonhole on `Nat.find`: if `firstHole S > |S|` then
`Finset.range (|S|+1) ⊆ S` (every `m ≤ |S|` lies below the first hole, hence in `S`), forcing
`|S|+1 ≤ |S|`. In the equality case `Finset.range |S| ⊆ S`, and `eq_of_subset_of_card_le` upgrades
the inclusion to equality; the converse is `firstHole_range`.

This records only the combinatorial first-hole characterization. The measure clause `μ(G(t)) = n^{−|S|}`
(measure sees only the budget, not the support position) and the metric formula `diam G(t) = 2^{−γ(S)}`
— whose equality case is read metrically as "prefix names uniquely minimize the diameter" — are the
atom's remaining, uncovered content. -/
theorem firstHole_le_card_and_eq_iff (S : Finset ℕ) :
    firstHole S ≤ S.card ∧ (firstHole S = S.card ↔ S = Finset.range S.card) := by
  have hbound : firstHole S ≤ S.card := by
    by_contra h
    simp only [not_le] at h
    have hsub : Finset.range (S.card + 1) ⊆ S := by
      intro m hm
      rw [Finset.mem_range] at hm
      by_contra hmS
      have hle : firstHole S ≤ m := by rw [firstHole]; exact Nat.find_le hmS
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  refine ⟨hbound, ?_, ?_⟩
  · intro h
    have hsub : Finset.range S.card ⊆ S := by
      intro m hm
      rw [Finset.mem_range] at hm
      by_contra hmS
      have hle : firstHole S ≤ m := by rw [firstHole]; exact Nat.find_le hmS
      rw [h] at hle
      omega
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_range S.card).symm)).symm
  · intro h
    conv_lhs => rw [h]
    rw [firstHole_range]

end D5.S0.Naming.FirstHoleBound
