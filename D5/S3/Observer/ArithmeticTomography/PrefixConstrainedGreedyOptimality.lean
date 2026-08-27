/- GID: D5/S3/Observer/ArithmeticTomography/PrefixConstrainedGreedyOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/ArithmeticTomography/PrefixConstrainedGreedyOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Antitone unit-cost cell gains admit a prefix-closed top-budget maximizer. -/

import Mathlib

/- Library-search audit trail (2026-08-27):
   * Repository searches for prefix-closed selections, top-budget cells, finite
     greedy optimality, and summed antitone gains found no exact D5 theorem.
     `GreedyResidualAllocation` proves only one-step weighted coverage, while
     `SmallPrimeChannelOptimality` treats complete equal-cost prime channels.
   * Body-shape searches for a finite selection closed under smaller depths and
     for exchange proofs on `Finset (Channel × Fin depth)` found no D5 primitive.
     This module introduces no `def` or `abbrev`.
   * Pinned Mathlib supplies `Finset.equivOfCardEq`, `Equiv.sum_comp`,
     `Finset.sum_erase_add`, and finite-sum monotonicity, but no theorem packaging
     the prefix-repair exchange and global top-budget conclusion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.ArithmeticTomography.PrefixConstrainedGreedyOptimality

universe u

/-- On finitely many channels and finitely many depth cells, a cardinality budget
is the unit-cost constraint. If gains are antitone down each channel and `top`
contains only gains at least as large as every omitted gain, then `top` can be
repaired to a prefix-closed selection without losing gain. The repaired selection
maximizes total gain among every selection with the same unit-cost budget. -/
theorem prefix_constrained_greedy_optimality
    {Channel : Type u} [Finite Channel]
    (depth budget : Nat) (gain : Channel → Fin depth → Real)
    (gain_antitone : ∀ channel, Antitone (gain channel))
    (top : Finset (Channel × Fin depth)) (top_card : top.card = budget)
    (top_dominates :
      ∀ inside ∈ top, ∀ outside ∉ top,
        gain outside.1 outside.2 ≤ gain inside.1 inside.2) :
    ∃ adjusted : Finset (Channel × Fin depth),
      adjusted.card = budget ∧
      (∀ channel level, (channel, level) ∈ adjusted →
        ∀ earlier, earlier < level → (channel, earlier) ∈ adjusted) ∧
      (∑ cell ∈ top, gain cell.1 cell.2) ≤
        ∑ cell ∈ adjusted, gain cell.1 cell.2 ∧
      ∀ competitor : Finset (Channel × Fin depth),
        competitor.card = budget →
          (∑ cell ∈ competitor, gain cell.1 cell.2) ≤
            ∑ cell ∈ adjusted, gain cell.1 cell.2 := by
  classical
  have repair :
      ∀ mass : Nat, ∀ selection : Finset (Channel × Fin depth),
        (∑ cell ∈ selection, cell.2.val) = mass →
        selection.card = budget →
        ∃ adjusted : Finset (Channel × Fin depth),
          adjusted.card = budget ∧
          (∀ channel level, (channel, level) ∈ adjusted →
            ∀ earlier, earlier < level → (channel, earlier) ∈ adjusted) ∧
          (∑ cell ∈ selection, gain cell.1 cell.2) ≤
            ∑ cell ∈ adjusted, gain cell.1 cell.2 := by
    intro mass
    induction mass using Nat.strong_induction_on with
    | h mass ih =>
        intro selection mass_eq selection_card
        by_cases prefix_closed :
            ∀ channel level, (channel, level) ∈ selection →
              ∀ earlier, earlier < level → (channel, earlier) ∈ selection
        · exact ⟨selection, selection_card, prefix_closed, le_rfl⟩
        · push Not at prefix_closed
          obtain ⟨channel, level, level_mem, earlier, earlier_lt, earlier_not_mem⟩ :=
            prefix_closed
          let removed : Channel × Fin depth := (channel, level)
          let inserted : Channel × Fin depth := (channel, earlier)
          let next := insert inserted (selection.erase removed)
          have removed_mem : removed ∈ selection := by
            simpa only [removed] using level_mem
          have inserted_not_selection : inserted ∉ selection := by
            simpa only [inserted] using earlier_not_mem
          have inserted_not_erase : inserted ∉ selection.erase removed := by
            intro inserted_mem
            exact inserted_not_selection (Finset.mem_of_mem_erase inserted_mem)
          have next_card : next.card = budget := by
            dsimp only [next]
            rw [Finset.card_insert_of_notMem inserted_not_erase,
              Finset.card_erase_of_mem removed_mem, selection_card]
            have selection_positive : 0 < selection.card :=
              Finset.card_pos.mpr ⟨removed, removed_mem⟩
            omega
          have next_mass :
              (∑ cell ∈ next, cell.2.val) < mass := by
            have erase_sum :=
              selection.sum_erase_add (fun cell => cell.2.val) removed_mem
            dsimp only [next]
            rw [Finset.sum_insert inserted_not_erase]
            dsimp only [inserted, removed] at erase_sum ⊢
            have depth_lt : earlier.val < level.val := earlier_lt
            omega
          have selection_gain_le_next :
              (∑ cell ∈ selection, gain cell.1 cell.2) ≤
                ∑ cell ∈ next, gain cell.1 cell.2 := by
            have erase_sum := selection.sum_erase_add
              (fun cell => gain cell.1 cell.2) removed_mem
            have gain_le : gain channel level ≤ gain channel earlier :=
              gain_antitone channel earlier_lt.le
            dsimp only [next]
            rw [Finset.sum_insert inserted_not_erase]
            dsimp only [inserted, removed] at erase_sum ⊢
            linarith
          obtain ⟨adjusted, adjusted_card, adjusted_prefix, next_gain_le⟩ :=
            ih (∑ cell ∈ next, cell.2.val) next_mass next rfl next_card
          exact ⟨adjusted, adjusted_card, adjusted_prefix,
            selection_gain_le_next.trans next_gain_le⟩
  obtain ⟨adjusted, adjusted_card, adjusted_prefix, top_gain_le⟩ :=
    repair (∑ cell ∈ top, cell.2.val) top rfl top_card
  have top_optimal :
      ∀ competitor : Finset (Channel × Fin depth),
        competitor.card = budget →
          (∑ cell ∈ competitor, gain cell.1 cell.2) ≤
            ∑ cell ∈ top, gain cell.1 cell.2 := by
    intro competitor competitor_card
    have difference_card :
        (competitor \ top).card = (top \ competitor).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff,
        Finset.inter_comm top competitor, competitor_card, top_card]
    let pairing : (competitor \ top : Finset (Channel × Fin depth)) ≃
        (top \ competitor : Finset (Channel × Fin depth)) :=
      Finset.equivOfCardEq difference_card
    have difference_sum :
        (∑ cell ∈ competitor \ top, gain cell.1 cell.2) ≤
          ∑ cell ∈ top \ competitor, gain cell.1 cell.2 := by
      calc
        (∑ cell ∈ competitor \ top, gain cell.1 cell.2) =
            ∑ cell : (competitor \ top : Finset (Channel × Fin depth)),
              gain cell.1.1 cell.1.2 := by
          rw [Finset.univ_eq_attach]
          exact (Finset.sum_attach (competitor \ top)
            (fun cell => gain cell.1 cell.2)).symm
        _ ≤ ∑ cell : (competitor \ top : Finset (Channel × Fin depth)),
              gain (pairing cell).1.1 (pairing cell).1.2 := by
          apply Finset.sum_le_sum
          intro cell _
          exact top_dominates (pairing cell).1
            (Finset.mem_sdiff.mp (pairing cell).2).1 cell.1
            (Finset.mem_sdiff.mp cell.2).2
        _ = ∑ cell : (top \ competitor : Finset (Channel × Fin depth)),
              gain cell.1.1 cell.1.2 := by
          exact pairing.sum_comp fun cell => gain cell.1.1 cell.1.2
        _ = ∑ cell ∈ top \ competitor, gain cell.1 cell.2 := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach (top \ competitor)
            (fun cell => gain cell.1 cell.2)
    have competitor_decomposition :
        competitor ∩ top ∪ (competitor \ top) = competitor := by
      ext cell
      by_cases in_top : cell ∈ top <;> simp [in_top]
    have top_decomposition :
        competitor ∩ top ∪ (top \ competitor) = top := by
      ext cell
      by_cases in_competitor : cell ∈ competitor <;> simp [in_competitor]
    have competitor_disjoint :
        Disjoint (competitor ∩ top) (competitor \ top) := by
      apply Finset.disjoint_left.mpr
      intro cell common added
      exact (Finset.mem_sdiff.mp added).2 (Finset.mem_inter.mp common).2
    have top_disjoint :
        Disjoint (competitor ∩ top) (top \ competitor) := by
      apply Finset.disjoint_left.mpr
      intro cell common removed
      exact (Finset.mem_sdiff.mp removed).2 (Finset.mem_inter.mp common).1
    calc
      (∑ cell ∈ competitor, gain cell.1 cell.2) =
          (∑ cell ∈ competitor ∩ top, gain cell.1 cell.2) +
            ∑ cell ∈ competitor \ top, gain cell.1 cell.2 := by
        rw [← Finset.sum_union competitor_disjoint, competitor_decomposition]
      _ ≤ (∑ cell ∈ competitor ∩ top, gain cell.1 cell.2) +
            ∑ cell ∈ top \ competitor, gain cell.1 cell.2 :=
        add_le_add_right difference_sum _
      _ = ∑ cell ∈ top, gain cell.1 cell.2 := by
        rw [← Finset.sum_union top_disjoint, top_decomposition]
  refine ⟨adjusted, adjusted_card, adjusted_prefix, top_gain_le, ?_⟩
  intro competitor competitor_card
  exact (top_optimal competitor competitor_card).trans top_gain_le

#print axioms prefix_constrained_greedy_optimality

end D5.S3.Observer.ArithmeticTomography.PrefixConstrainedGreedyOptimality
