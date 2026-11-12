/- GID: D5/S3/Arith/Robin/PriceRecord/ActualArbitraryBracketTwoTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualArbitraryBracketTwoTail
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Unconditional asymptotic full binary tails of original strict records. -/

import D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail

open Real Filter
open scoped Topology
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.Robin.EulerLayerInventoryGrowth
open D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

/-- The global case has zero gap. The non-global case uses the actual greatest
feasible optimizer and the original strict predecessor record. -/
private theorem finite_tail_gap {m : ℕ} (hm : 1 ≤ m) {c mu s : ℝ}
    (hc : 0 < c) (hmu : 0 < mu) (hs : 0 < s)
    (ha : optimalLayerCount c 2 ≤ m.factorization 2)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s) :
    ∃ g : ℝ, 0 ≤ g ∧ s * g * exp g < 1 ∧
      h2 m c < g + 2 * (c / s) * log 2 := by
  obtain ⟨hn, _, _, hdelete⟩ := full_original2tail_deletion_identity hm ha s
  have hreward := (full_original2tail_reward_bound hc ha).2
  have hidentity := reward_deficit_identity m c
  by_cases hglobal : IsGoldenResourceOptimal s m
  · refine ⟨0, le_rfl, by simp, ?_⟩
    have hcomp := hglobal (deleted2tailInteger m c) hn
    have hbudget : s * h2 m c < 2 * c * log 2 := by linarith
    have hcancel : s * (2 * (c / s) * log 2) = 2 * c * log 2 := by
      field_simp
    have hlt : h2 m c < 2 * (c / s) * log 2 := by
      exact (mul_lt_mul_iff_right₀ hs).mp (by linarith only [hbudget, hcancel])
    simpa using hlt
  · obtain ⟨C, hgap⟩ := greatest_feasible_global_gap hs hA hD hglobal
    let g := log ((m : ℝ) / C)
    have hg : 0 < g := hgap.gap_pos
    have hstrict := hrecord C (by have := hgap.positive; omega) hgap.below
    have htransfer := objective_price_difference mu s hm hgap.positive
    have hupper : goldenResourceObjective s C - goldenResourceObjective s m <
        (s - mu) * g := by rw [htransfer]; dsimp only [g]; linarith
    have hnonneg := hgap.global m hm
    have hsmu : mu < s := by
      have hpos : 0 < (s - mu) * g := by linarith
      exact sub_pos.mp ((mul_pos_iff_of_pos_right hg).mp hpos)
    have hcomp := hgap.global (deleted2tailInteger m c) hn
    have hbudget : s * h2 m c < s * g + 2 * c * log 2 := by
      have hmg := mul_pos hmu hg
      nlinarith only [hcomp, hdelete, hupper, hidentity, hreward, hmg]
    refine ⟨g, hg.le, hgap.exponential_bound, ?_⟩
    apply (mul_lt_mul_iff_right₀ hs).mp
    have hcancel : s * (g + 2 * (c / s) * log 2) = s * g + 2 * c * log 2 := by
      field_simp
      <;> ring
    linarith only [hbudget, hcancel]

end D5.S3.Arith.Robin.PriceRecord.ActualArbitraryBracketTwoTail
