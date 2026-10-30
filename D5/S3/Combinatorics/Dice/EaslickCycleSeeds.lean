/- GID: D5/S3/Combinatorics/Dice/EaslickCycleSeeds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/EaslickCycleSeeds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.List.Chain]
   utility: none
   digest: Fixed simple cycles supply the finite seeds for minimal-advantage padding. -/

import D5.S3.Combinatorics.Dice.EaslickMinimalAdvantage
import Mathlib.Data.List.Chain

/-! The seven- through ten-face cycle data are by Terry Easlick,
arXiv:2610.40321v1, Appendices G--J, https://arxiv.org/html/2610.40321v1,
CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
The six-face cycle is an exact count construction. The eleven-face cycle is derived
from the seven-face source cycle by shifting labels and adding nested extremes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.EaslickCycleSeeds
open EaslickMinimalAdvantage

/-- Six fixed seed cycles, each without a duplicated closure row. -/
def sourceSeed : ℕ → List (List ℕ)
  | 6 => [
    [1, 1, 2, 5, 5, 5],
    [1, 3, 4, 4, 4, 4],
    [2, 2, 2, 3, 6, 6],
    [1, 1, 2, 5, 5, 6],
    [1, 3, 3, 4, 4, 4],
    [2, 2, 3, 3, 3, 6]]
  | 7 => [
    [1, 1, 1, 3, 3, 4, 7],
    [2, 2, 2, 2, 2, 2, 6],
    [1, 1, 1, 3, 5, 5, 5],
    [1, 1, 2, 2, 4, 4, 4],
    [1, 1, 3, 3, 3, 3, 3],
    [1, 2, 2, 2, 2, 5, 6],
    [1, 1, 1, 4, 4, 4, 5],
    [1, 1, 3, 3, 3, 3, 4],
    [1, 2, 2, 2, 2, 5, 7],
    [1, 1, 1, 4, 4, 4, 6],
    [1, 1, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 3, 5, 5, 6],
    [2, 2, 2, 2, 3, 4, 4]]
  | 8 => [
    [1, 1, 1, 2, 4, 6, 6, 6],
    [1, 1, 3, 3, 3, 3, 3, 5],
    [2, 2, 2, 2, 2, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 7, 8],
    [2, 2, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 2, 5, 5, 5, 6],
    [1, 2, 3, 3, 3, 4, 4, 4],
    [2, 2, 2, 2, 2, 3, 6, 6],
    [1, 1, 1, 2, 5, 5, 5, 7],
    [1, 2, 3, 3, 4, 4, 4, 4],
    [1, 2, 2, 2, 3, 3, 6, 6],
    [1, 1, 1, 2, 5, 5, 5, 5],
    [1, 2, 3, 4, 4, 4, 4, 4],
    [1, 2, 3, 3, 3, 3, 4, 6],
    [2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 3, 4, 4, 8, 8],
    [2, 2, 2, 2, 2, 3, 6, 7],
    [1, 1, 1, 2, 5, 5, 5, 8],
    [1, 2, 4, 4, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 6, 7, 7],
    [2, 2, 2, 2, 2, 5, 5, 6],
    [1, 1, 1, 4, 4, 4, 6, 7],
    [1, 1, 3, 3, 3, 3, 5, 6],
    [2, 2, 2, 2, 2, 4, 5, 8],
    [1, 1, 1, 3, 3, 7, 7, 7],
    [2, 2, 2, 2, 2, 2, 6, 8],
    [1, 1, 1, 3, 5, 5, 5, 6],
    [1, 3, 3, 3, 3, 4, 4, 4],
    [2, 2, 2, 3, 3, 3, 3, 7]]
  | 9 => [
    [1, 1, 1, 1, 3, 3, 3, 3, 7],
    [2, 2, 2, 2, 2, 2, 2, 2, 6],
    [1, 1, 1, 1, 3, 5, 5, 5, 5],
    [1, 1, 2, 2, 2, 4, 4, 4, 4],
    [1, 1, 1, 2, 3, 3, 3, 3, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 7],
    [1, 1, 1, 1, 3, 3, 6, 6, 6],
    [2, 2, 2, 2, 2, 2, 2, 4, 5],
    [1, 1, 1, 1, 3, 3, 4, 5, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 8]]
  | 10 => [
    [1, 1, 1, 1, 2, 4, 4, 4, 4, 4],
    [1, 2, 2, 3, 3, 3, 3, 3, 3, 3],
    [1, 2, 2, 2, 2, 2, 2, 4, 7, 7],
    [1, 1, 1, 1, 3, 3, 3, 6, 6, 6],
    [1, 2, 2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 1, 2, 4, 4, 4, 4, 5],
    [1, 2, 3, 3, 3, 3, 3, 3, 3, 3],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 7],
    [1, 1, 1, 1, 2, 4, 5, 5, 5, 6],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 4],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 6],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 6],
    [1, 2, 2, 2, 2, 2, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 5],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 7],
    [1, 1, 1, 1, 3, 3, 3, 6, 6, 7],
    [2, 2, 2, 2, 2, 2, 2, 4, 5, 5],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 7],
    [1, 1, 1, 1, 3, 4, 4, 5, 5, 6],
    [1, 2, 2, 3, 3, 3, 3, 3, 3, 4],
    [1, 2, 2, 2, 2, 2, 2, 4, 8, 8],
    [1, 1, 1, 1, 3, 3, 3, 6, 7, 7],
    [2, 2, 2, 2, 2, 2, 2, 5, 5, 5],
    [1, 1, 1, 2, 2, 4, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 6],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 8],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 8],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 7],
    [1, 2, 2, 2, 2, 3, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 7],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 7],
    [1, 1, 1, 1, 3, 4, 4, 5, 5, 5],
    [2, 2, 2, 3, 3, 3, 3, 3, 3, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 8],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 6],
    [1, 1, 2, 3, 3, 3, 3, 3, 4, 4],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 7],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 8],
    [1, 2, 2, 2, 2, 4, 4, 4, 4, 4],
    [1, 1, 1, 1, 3, 3, 3, 4, 7, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 9],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 7],
    [1, 2, 2, 3, 3, 3, 3, 3, 4, 4],
    [1, 2, 2, 2, 2, 2, 2, 4, 8, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 7],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 6],
    [1, 1, 1, 1, 4, 4, 4, 5, 5, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 5],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 8],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 9],
    [1, 2, 2, 2, 3, 3, 4, 4, 4, 4],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 8],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 8],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 6],
    [1, 1, 2, 3, 3, 3, 3, 3, 4, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 9, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 8],
    [1, 2, 2, 2, 2, 2, 2, 6, 6, 6],
    [1, 1, 1, 1, 2, 5, 5, 5, 5, 10],
    [1, 2, 2, 2, 3, 4, 4, 4, 4, 4],
    [1, 1, 1, 1, 3, 3, 3, 4, 8, 9],
    [2, 2, 2, 2, 2, 2, 2, 2, 7, 8],
    [1, 1, 1, 1, 2, 4, 6, 6, 6, 7],
    [1, 1, 1, 3, 3, 3, 3, 3, 5, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 9, 10],
    [1, 1, 1, 1, 3, 3, 3, 7, 8, 8],
    [2, 2, 2, 2, 2, 2, 2, 2, 6, 10],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 8],
    [1, 2, 3, 3, 3, 3, 3, 3, 3, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 9],
    [1, 1, 1, 1, 3, 5, 5, 5, 5, 6],
    [1, 1, 1, 2, 2, 4, 4, 4, 4, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 9],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 9],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 7],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 6],
    [2, 2, 2, 2, 2, 2, 2, 3, 6, 9],
    [1, 1, 1, 1, 2, 5, 5, 5, 6, 6],
    [1, 2, 2, 2, 4, 4, 4, 4, 4, 4],
    [1, 1, 1, 2, 3, 3, 3, 4, 8, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 7, 9],
    [1, 1, 1, 1, 2, 4, 6, 6, 6, 8],
    [1, 1, 2, 3, 3, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 2, 2, 4, 10, 10],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 9],
    [2, 2, 2, 2, 2, 2, 2, 4, 5, 6],
    [1, 1, 1, 1, 3, 3, 3, 4, 9, 10],
    [2, 2, 2, 2, 2, 2, 2, 2, 8, 9],
    [1, 1, 1, 1, 2, 4, 6, 6, 7, 8],
    [1, 1, 3, 3, 3, 3, 3, 3, 3, 5],
    [1, 2, 2, 2, 2, 2, 4, 4, 4, 5],
    [1, 1, 1, 3, 3, 3, 3, 3, 3, 10],
    [1, 2, 2, 2, 2, 2, 2, 5, 6, 10],
    [1, 1, 1, 1, 4, 4, 4, 4, 5, 8],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 7],
    [1, 2, 2, 2, 2, 2, 2, 6, 6, 7],
    [1, 1, 1, 1, 3, 3, 5, 5, 5, 10],
    [2, 2, 2, 2, 2, 2, 2, 4, 4, 9],
    [1, 1, 1, 1, 3, 3, 3, 7, 7, 10],
    [2, 2, 2, 2, 2, 2, 2, 4, 6, 6],
    [1, 1, 1, 1, 3, 4, 5, 5, 5, 9],
    [2, 2, 2, 3, 3, 3, 3, 3, 4, 4],
    [1, 1, 1, 2, 2, 2, 6, 7, 7, 10],
    [1, 1, 1, 1, 4, 4, 4, 5, 5, 6],
    [1, 1, 1, 3, 3, 3, 3, 3, 4, 8],
    [1, 2, 2, 2, 2, 2, 2, 5, 7, 8],
    [1, 1, 1, 1, 3, 4, 4, 4, 6, 7],
    [2, 2, 2, 2, 3, 3, 3, 3, 3, 5]]
  | 11 => [
    [1, 1, 3, 3, 3, 5, 5, 6, 9, 11, 11],
    [2, 2, 4, 4, 4, 4, 4, 4, 8, 10, 10],
    [1, 1, 3, 3, 3, 5, 7, 7, 7, 11, 11],
    [2, 2, 3, 3, 4, 4, 6, 6, 6, 10, 10],
    [1, 1, 3, 3, 5, 5, 5, 5, 5, 11, 11],
    [2, 2, 3, 4, 4, 4, 4, 7, 8, 10, 10],
    [1, 1, 3, 3, 3, 6, 6, 6, 7, 11, 11],
    [2, 2, 3, 3, 5, 5, 5, 5, 6, 10, 10],
    [1, 1, 3, 4, 4, 4, 4, 7, 9, 11, 11],
    [2, 2, 3, 3, 3, 6, 6, 6, 8, 10, 10],
    [1, 1, 3, 3, 5, 5, 5, 5, 7, 11, 11],
    [2, 2, 3, 4, 4, 4, 4, 8, 9, 10, 10],
    [1, 1, 3, 3, 3, 5, 7, 7, 8, 11, 11],
    [2, 2, 4, 4, 4, 4, 5, 6, 6, 10, 10]]
  | _ => []

private def IsScoreCycle (n : ℕ) (c : List (List ℕ)) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ (∀ d ∈ c, IsDie n d) ∧
    (c ++ [c.head!]).IsChain (fun d e => winCount d e = threshold n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Finite source lists are checked by kernel reduction. -/
private theorem sourceSeed_score (n : ℕ) (hn : n ∈ [6,7,8,9,10,11]) :
    IsScoreCycle n (sourceSeed n) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold IsScoreCycle IsDie <;> decide

private theorem hasCycle_of_score (n : ℕ) (hn : 3 ≤ n) (c : List (List ℕ))
    (h : IsScoreCycle n c) : HasCycle n c.length := by
  obtain ⟨hne,hnodup,hvalid,hchain⟩ := h
  have hhead : c.head! ∈ c := by
    cases c with
    | nil => contradiction
    | cons a l => simp
  have hv (d : List ℕ) (hd : d ∈ c ++ [c.head!]) : IsDie n d := by
    rcases List.mem_append.mp hd with hmem | hmem
    · exact hvalid d hmem
    · have : d = c.head! := by simpa using hmem
      rw [this]
      exact hvalid _ hhead
  refine ⟨c,rfl,hnodup,hne,?_⟩
  exact hchain.imp_of_mem_imp (fun a b ha hb hab =>
    (edge_iff n hn a b (hv a ha) (hv b hb)).mpr hab)

/-- These finite witnesses are ingredients for the full parameter cover. -/
theorem finite_cycle_witnesses :
    HasCycle 6 6 ∧ HasCycle 7 14 ∧ HasCycle 8 29 ∧
      HasCycle 9 10 ∧ HasCycle 10 110 ∧ HasCycle 11 14 := by
  exact ⟨hasCycle_of_score 6 (by decide) _ (sourceSeed_score 6 (by decide)),
    hasCycle_of_score 7 (by decide) _ (sourceSeed_score 7 (by decide)),
    hasCycle_of_score 8 (by decide) _ (sourceSeed_score 8 (by decide)),
    hasCycle_of_score 9 (by decide) _ (sourceSeed_score 9 (by decide)),
    hasCycle_of_score 10 (by decide) _ (sourceSeed_score 10 (by decide)),
    hasCycle_of_score 11 (by decide) _ (sourceSeed_score 11 (by decide))⟩

end D5.S3.Combinatorics.Dice.EaslickCycleSeeds
