/- GID: D5/S3/StatisticalMechanics/HardCore/CompleteStraightPathCounts
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/CompleteStraightPathCounts
   mirror-E: none(waiver:symbolic-straight-path-induction)
   anchors: []
   utility: none
   digest: Complete parent-root counts are positive and bounded by three to the depth. -/

import D5.S3.StatisticalMechanics.HardCore.MemoryBlockBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.CompleteStraightPathCounts

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.MemoryRefinement
open D5.S3.StatisticalMechanics.HardCore.MemoryLightCone
open D5.S3.StatisticalMechanics.HardCore.MemoryBlockBounds

/-- For each of the six fixed relative orderings, the complete process from
the parent blocker has a straight continuation at every depth. Both its count
and every positive-radius geometric-memory count are at most three to the depth. -/
theorem complete_straight_path_bounds (a : Fin 6) (n : ℕ) :
    1 ≤ pathCount completeStep (fun _ _ => a) n [] {(-1, 0)} ∧
    pathCount completeStep (fun _ _ => a) n [] {(-1, 0)} ≤ 3 ^ n ∧
    ∀ r : ℕ, 1 ≤ r →
      pathCount (geometricStep r) (fun _ _ => a) n [] {(-1, 0)} ≤ 3 ^ n := by
  have hpositive : ∀ (m : ℕ) (h : List (Fin 3)) (F : Finset Point),
      (∀ p ∈ F, p.1 ≤ 0) →
        1 ≤ pathCount completeStep (fun _ _ => a) m h F := by
    intro m
    induction m with
    | zero => intro h F _; simp [pathCount]
    | succ m ih =>
        intro h F hF
        have hd : direction (0 : Fin 3) ∉ F := by
          intro hm
          have hb := hF _ hm
          norm_num [direction] at hb
        have hc : ∀ p ∈ ((F ∪ deleted a 0).image (recenter 0)), p.1 ≤ 0 := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
          have hqx : q.1 ≤ 1 := by
            rcases Finset.mem_union.mp hq with hqF | hqD
            · have hb := hF q hqF
              omega
            · rcases Finset.mem_insert.mp hqD with hqO | hqDirs
              · subst q; norm_num
              · rcases Finset.mem_image.mp hqDirs with ⟨e, _, rfl⟩
                simp only [direction]
                split_ifs <;> norm_num
          simp only [recenter, Fin.isValue, ↓reduceIte]
          omega
        have hterm : 1 ≤ (completeStep F a 0).elim 0
            (pathCount completeStep (fun _ _ => a) m (0 :: h)) := by
          simpa only [completeStep, if_neg hd, Option.elim_some] using
            ih (0 :: h) ((F ∪ deleted a 0).image (recenter 0)) hc
        simp only [pathCount]
        exact hterm.trans (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun d : Fin 3 => (completeStep F a d).elim 0
            (pathCount completeStep (fun _ _ => a) m (d :: h)))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin 3)))
  have hgeometric : ∀ r : ℕ, 1 ≤ r →
      pathCount (geometricStep r) (fun _ _ => a) n [] {(-1, 0)} ≤ 3 ^ n := by
    intro r hr
    simpa using fixed_order_block_bound r 1 hr hr a 0 n [] {(-1, 0)} (by simp)
  refine ⟨hpositive n [] {(-1, 0)} (by simp), ?_, hgeometric⟩
  exact (complete_count_le_memory 1 (fun _ => a) n []
    {(-1, 0)} {(-1, 0)} (Finset.Subset.refl _)).trans (hgeometric 1 le_rfl)

#print axioms complete_straight_path_bounds

end D5.S3.StatisticalMechanics.HardCore.CompleteStraightPathCounts
