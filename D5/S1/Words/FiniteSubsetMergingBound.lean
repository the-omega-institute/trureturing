/- GID: D5/S1/Words/FiniteSubsetMergingBound
   generality: G
   mirror-B: D5/B/S1/Words/FiniteSubsetMergingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pairwise length bounds give a quantitative merging word for finite uncertainty sets. -/

import Mathlib.Data.Finset.Card

/-! # Quantitative merging of finite uncertainty sets -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.FiniteSubsetMergingBound

universe u v

/-- Concatenating pair-merging words synchronizes any finite uncertainty set,
with one length-L budget for each state after the first. -/
theorem exists_merging_word_length_le
    {σ : Type u} {α : Type v} (step : σ → α → σ) (L : Nat) (S : Finset σ)
    (pairwise : ∀ x y : σ, ∃ w : List α,
      w.length ≤ L ∧ w.foldl step x = w.foldl step y) :
    ∃ w : List α, w.length ≤ (S.card - 1) * L ∧
      ∀ x ∈ S, ∀ y ∈ S, w.foldl step x = w.foldl step y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨[], Nat.zero_le _, by simp⟩
  | @insert a S ha ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨b, hb⟩ := hS
        obtain ⟨u, hu, hmerge⟩ := ih
        obtain ⟨v, hv, hab⟩ := pairwise (u.foldl step a) (u.foldl step b)
        refine ⟨u ++ v, ?_, ?_⟩
        · calc
            (u ++ v).length = u.length + v.length := List.length_append
            _ ≤ (S.card - 1) * L + L := Nat.add_le_add hu hv
            _ = S.card * L := by
              rw [← Nat.add_one_mul, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨b, hb⟩)]
            _ = ((insert a S).card - 1) * L := by
              rw [Finset.card_insert_of_notMem ha, Nat.add_sub_cancel]
        · have toRepresentative : ∀ x ∈ insert a S,
              (u ++ v).foldl step x = v.foldl step (u.foldl step b) := by
            intro x hx
            rw [List.foldl_append]
            rcases Finset.mem_insert.mp hx with hxa | hxS
            · subst x
              exact hab
            · rw [hmerge x hxS b hb]
          intro x hx y hy
          exact (toRepresentative x hx).trans (toRepresentative y hy).symm
      · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        refine ⟨[], Nat.zero_le _, ?_⟩
        intro x hx y hy
        have hx' : x = a := by simpa using hx
        have hy' : y = a := by simpa using hy
        rw [hx', hy']

end D5.S1.Words.FiniteSubsetMergingBound
