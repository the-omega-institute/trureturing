/- GID: D5/S1/Words/FiniteSubsetCompressionBound
   generality: G
   mirror-B: D5/B/S1/Words/FiniteSubsetCompressionBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite uncertainty compression with arbitrary costs at each rank. -/

import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Rank-dependent compression of finite uncertainty sets -/

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.FiniteSubsetCompressionBound

universe u v

/-- A strict cardinality reduction at each rank yields a bounded word reducing
the uncertainty set to at most one point, with the exact sum of the costs of
the ranks that can occur. -/
theorem exists_compressing_word_length_le
    {σ : Type u} {α : Type v} [DecidableEq σ]
    (step : σ → α → σ) (C : Nat → Nat) (S : Finset σ)
    (compress : ∀ T : Finset σ, 2 ≤ T.card →
      ∃ w : List α, w.length ≤ C T.card ∧
        (T.image (fun x => w.foldl step x)).card < T.card) :
    ∃ w : List α, w.length ≤ ∑ k ∈ Finset.range (S.card - 1), C (k + 2) ∧
      (S.image (fun x => w.foldl step x)).card ≤ 1 := by
  classical
  let P : Nat → Prop := fun n => ∀ T : Finset σ, T.card = n →
    ∃ w : List α, w.length ≤ ∑ k ∈ Finset.range (T.card - 1), C (k + 2) ∧
      (T.image (fun x => w.foldl step x)).card ≤ 1
  have hsum : ∀ m n : Nat, m ≤ n →
      (∑ k ∈ Finset.range m, C (k + 2)) ≤
        ∑ k ∈ Finset.range n, C (k + 2) := by
    have hsum_aux : ∀ m d : Nat,
        (∑ k ∈ Finset.range m, C (k + 2)) ≤
          ∑ k ∈ Finset.range (m + d), C (k + 2) := by
      intro m d
      induction d with
      | zero => simp
      | succ d ih =>
          rw [Nat.add_succ, Finset.sum_range_succ]
          exact ih.trans (Nat.le_add_right _ _)
    intro m n hmn
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hmn
    rw [hd]
    exact hsum_aux m d
  have hmain : P S.card := by
    unfold P
    refine Nat.strong_induction_on S.card
      (p := fun n => ∀ T : Finset σ, T.card = n →
        ∃ w : List α, w.length ≤ ∑ k ∈ Finset.range (T.card - 1), C (k + 2) ∧
          (T.image (fun x => w.foldl step x)).card ≤ 1) ?_
    intro n ih T hT
    by_cases hsmall : T.card ≤ 1
    · refine ⟨[], Nat.zero_le _, ?_⟩
      exact (Finset.card_image_le.trans hsmall)
    · have htwo : 2 ≤ T.card := by omega
      obtain ⟨u, hu, hreduce⟩ := compress T htwo
      let U := T.image (fun x => u.foldl step x)
      have hUcard : U.card < T.card := by
        exact hreduce
      obtain ⟨v, hv, hvfinal⟩ := ih U.card (by omega) U rfl
      have hindex : U.card - 1 ≤ T.card - 2 := by omega
      have hsum' : (∑ k ∈ Finset.range (U.card - 1), C (k + 2)) ≤
          ∑ k ∈ Finset.range (T.card - 2), C (k + 2) := hsum _ _ hindex
      refine ⟨u ++ v, ?_, ?_⟩
      · rw [List.length_append]
        calc
          u.length + v.length ≤ C T.card +
              ∑ k ∈ Finset.range (U.card - 1), C (k + 2) :=
            Nat.add_le_add hu hv
          _ ≤ C T.card + ∑ k ∈ Finset.range (T.card - 2), C (k + 2) :=
            Nat.add_le_add_left hsum' _
          _ = ∑ k ∈ Finset.range (T.card - 1), C (k + 2) := by
            rw [show T.card - 1 = (T.card - 2) + 1 by omega,
              Finset.sum_range_succ]
            rw [show T.card - 2 + 2 = T.card by omega, Nat.add_comm]
      · have himage : T.image (fun x => (u ++ v).foldl step x) =
            U.image (fun x => v.foldl step x) := by
          simp [U, List.foldl_append, Finset.image_image, Function.comp_def]
        rw [himage]
        exact hvfinal
  exact hmain S rfl

end D5.S1.Words.FiniteSubsetCompressionBound
