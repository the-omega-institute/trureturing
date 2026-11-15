/- GID: D5/S1/Words/RankedCostDescent
   generality: G
   mirror-B: D5/B/S1/Words/RankedCostDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An independent rank constructs a goal word with a state-dependent cost budget. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankedCostDescent

universe u v

/-- Accumulate each letter's charge at the state in which it is executed. -/
def wordCost {σ : Type u} {α : Type v}
    (step : σ → α → σ) (charge : σ → α → Nat) : σ → List α → Nat
  | _, [] => 0
  | s, a :: w => charge s a + wordCost step charge (step s a) w

private theorem wordCost_append {σ : Type u} {α : Type v}
    (step : σ → α → σ) (charge : σ → α → Nat)
    (s : σ) (a b : List α) :
    wordCost step charge s (a ++ b) =
      wordCost step charge s a + wordCost step charge (a.foldl step s) b := by
  induction a generalizing s with
  | nil => simp [wordCost]
  | cons x a ih => simp [wordCost, ih, Nat.add_assoc]

/-- Rank descent ensures termination while a separate potential pays the
state-dependent charges, including zero charges, along the constructed word. -/
theorem exists_goal_word_cost_add_potential_le
    {σ : Type u} {α : Type v}
    (step : σ → α → σ) (Goal : σ → Prop) (rank potential : σ → Nat)
    (charge : σ → α → Nat) (start : σ)
    (progress : ∀ s, ¬ Goal s → ∃ a : List α,
      rank (a.foldl step s) < rank s ∧
      wordCost step charge s a + potential (a.foldl step s) ≤ potential s) :
    ∃ w : List α, Goal (w.foldl step start) ∧
      wordCost step charge start w + potential (w.foldl step start) ≤
        potential start := by
  classical
  have descend (n : Nat) : ∀ s, rank s = n →
      ∃ w : List α, Goal (w.foldl step s) ∧
        wordCost step charge s w + potential (w.foldl step s) ≤ potential s := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hgoal : Goal s
      · exact ⟨[], hgoal, by simp [wordCost]⟩
      · obtain ⟨a, hdrop, hcost⟩ := progress s hgoal
        obtain ⟨b, hgoal', hbudget⟩ :=
          ih (rank (a.foldl step s)) (by omega) (a.foldl step s) rfl
        refine ⟨a ++ b, ?_, ?_⟩
        · simpa only [List.foldl_append] using hgoal'
        · rw [wordCost_append, List.foldl_append]
          omega
  exact descend (rank start) start rfl

end D5.S1.Words.RankedCostDescent
