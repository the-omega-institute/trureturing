/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Actual finite subgroups inherit certified prefix-product lower bounds. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.GroupState
import D5.S3.Arith.Divisors.MakowskiSchinzel.SupportModel
import Mathlib.Tactic

/-! Rank domination transfers checked prefix products to arbitrary actual finite subsets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset

/-- Every finite subset is rank-dominated by the equally long initial table segment. -/
theorem finite_subgroup_bound {qs : List ℕ} (hs : qs.Pairwise (· ≤ ·))
    (F : Finset ℕ) (hF : ∀ q ∈ F, q ∈ qs) :
    Certificate.lowerProduct (qs.take F.card) ≤
      Certificate.lowerProduct (F.sort (· ≤ ·)) := by
  have hlen : (F.sort (· ≤ ·)).length ≤ qs.length := by
    rw [length_sort]
    exact (card_le_card (show F ⊆ qs.toFinset from
      fun q hq => List.mem_toFinset.mpr (hF q hq))).trans qs.toFinset_card_le
  have hrank := Certificate.ranks_of_saturated hs F.sortedLT_sort.pairwise hlen
    (fun q hq _ => hF q (by simpa using hq))
  have hmono := Certificate.lowerProduct_mono hrank
  rw [length_sort] at hmono
  exact hmono

/-- Every actual finite subgroup receives its checked prefix and product lower bound. -/
theorem table_group_prefix_bound (T : List ℕ) (tl : List (ℕ × ℕ × ℕ))
    (fs : List (ℕ × ℕ)) (t : ℕ × ℕ × ℕ) (F : Finset ℕ) {i p : ℕ}
    (hs : (groupValues i T).Pairwise (· ≤ ·))
    (hrun : stepTable tl T initialState = some fs)
    (hfinal : F.card = (groupValues i T).length →
      ∀ j L, fs[i]? = some (j, L) → prefixOk p j L t = true)
    (hp : oddPrimes[i]? = some p) (ht : tl[i]? = some t)
    (hF : ∀ q ∈ F, q ∈ groupValues i T) :
    prefixOk p F.card (fixedProduct scale ((groupValues i T).take F.card))
        t = true ∧
      (fixedProduct scale ((groupValues i T).take F.card) : ℝ) / scale ≤
        (Certificate.lowerProduct (F.sort (· ≤ ·)) : ℝ) := by
  let qs := groupValues i T
  have hsorted : qs.Pairwise (· ≤ ·) := hs
  have hlen : F.card ≤ qs.length :=
    (card_le_card (show F ⊆ qs.toFinset from
      fun q hq => List.mem_toFinset.mpr (hF q hq))).trans qs.toFinset_card_le
  have hstart : initialState[i]? = some (0, scale) := by
    simp only [initialState, List.getElem?_map, hp, Option.map_some]
  obtain ⟨hend, hproper⟩ := stepTable_group hrun hp hstart ht
  refine ⟨?_, ?_⟩
  · by_cases hfull : F.card = (groupValues i T).length
    · have hlast := hfinal hfull _ _ hend
      simpa only [Nat.zero_add] using
        (stepTable_all_prefixes hrun hp hstart ht).mpr hlast F.card hlen
    · simpa only [Nat.zero_add] using
        hproper F.card (lt_of_le_of_ne hlen hfull)
  · have hb := finite_subgroup_bound hsorted F hF
    have hs0 : (0 : ℚ) < scale := by norm_num [scale]
    have hround : (fixedProduct scale ((groupValues i T).take F.card) : ℚ) / scale ≤
        Certificate.lowerProduct ((groupValues i T).take F.card) := by
      apply (div_le_iff₀ hs0).mpr
      simpa only [Certificate.lowerProduct, mul_comm] using
        fixedProduct_le scale ((groupValues i T).take F.card)
    have hb' := (Rat.cast_le (K := ℝ)).mpr (hround.trans hb)
    simpa only [Rat.cast_div, Rat.cast_natCast] using hb'

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
