/- GID: D5/S3/StatisticalMechanics/HardCore/MemoryLightCone
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/MemoryLightCone
   mirror-E: none(waiver:symbolic-finite-propagation)
   anchors: []
   digest: Finite geometric memory reproduces every fixed-depth complete deletion count. -/

import D5.S3.StatisticalMechanics.HardCore.MemoryRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.MemoryLightCone

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.MemoryRefinement

/-- Manhattan distance from the current vertex. -/
def gridRadius (p : Point) : ℕ := p.1.natAbs + p.2.natAbs

private theorem abs_pred_bound (x : ℤ) : x.natAbs ≤ (x - 1).natAbs + 1 := by
  calc
    x.natAbs = ((x - 1) + 1).natAbs := by congr 1 <;> omega
    _ ≤ (x - 1).natAbs + (1 : ℤ).natAbs := Int.natAbs_add_le _ _
    _ = _ := by norm_num

private theorem abs_succ_bound (x : ℤ) : x.natAbs ≤ (x + 1).natAbs + 1 := by
  calc
    x.natAbs = ((x + 1) + (-1)).natAbs := by congr 1 <;> omega
    _ ≤ (x + 1).natAbs + (-1 : ℤ).natAbs := Int.natAbs_add_le _ _
    _ = _ := by norm_num

/-- A single recentering can bring a recorded point closer by at most one. -/
theorem recenter_radius_bound (d : Fin 3) (p : Point) :
    gridRadius p ≤ gridRadius (recenter d p) + 1 := by
  have hx := abs_pred_bound p.1
  have hy := abs_pred_bound p.2
  have hp := abs_succ_bound p.2
  have hn : (-p.2 - 1).natAbs = (p.2 + 1).natAbs := by
    rw [show -p.2 - 1 = -(p.2 + 1) by ring]
    simp
  fin_cases d <;> simp [gridRadius, recenter, hn] <;> omega

/-- The blocker sets agree on every vertex that can be reached within n steps. -/
def AgreeWithin (n : ℕ) (F G : Finset Point) : Prop :=
  ∀ p, gridRadius p ≤ n → (p ∈ F ↔ p ∈ G)

private theorem image_agrees (n : ℕ) (F G : Finset Point)
    (a : Fin 6) (d : Fin 3) (hFG : AgreeWithin (n + 1) F G) :
    AgreeWithin n ((F ∪ deleted a d).image (recenter d))
      ((G ∪ deleted a d).image (recenter d)) := by
  intro p hp
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨q, hq, heq⟩
    have hqrad : gridRadius q ≤ n + 1 := by
      have hqrad := recenter_radius_bound d q
      rw [heq] at hqrad
      omega
    exact Finset.mem_image.mpr ⟨q,
      by simpa only [Finset.mem_union, hFG q hqrad] using hq, heq⟩
  · intro h
    rcases Finset.mem_image.mp h with ⟨q, hq, heq⟩
    have hqrad : gridRadius q ≤ n + 1 := by
      have hqrad := recenter_radius_bound d q
      rw [heq] at hqrad
      omega
    exact Finset.mem_image.mpr ⟨q,
      by simpa only [Finset.mem_union, hFG q hqrad] using hq, heq⟩

/-- Local agreement persists on the smaller light cone, including unequal
retention radii. This states agreement, not equality of the complete memories. -/
theorem memoryStep_agreeWithin (n r R : ℕ) (hr : n ≤ r) (hR : n ≤ R)
    (F G : Finset Point) (a : Fin 6) (d : Fin 3)
    (hFG : AgreeWithin (n + 1) F G) :
    AgreeWithin n (memoryStep r F a d) (memoryStep R G a d) := by
  intro p hp
  change (p ∈ ((F ∪ deleted a d).image (recenter d)).filter
      (fun q => gridRadius q ≤ r)) ↔
    (p ∈ ((G ∪ deleted a d).image (recenter d)).filter
      (fun q => gridRadius q ≤ R))
  simp only [Finset.mem_filter]
  exact and_congr (image_agrees n F G a d hFG p hp)
    (iff_of_true (hp.trans hr) (hp.trans hR))

/-- Complete ordered blocker accumulation. No old blocker is forgotten. -/
def completeStep (F : Finset Point) (a : Fin 6) (d : Fin 3) :
    Option (Finset Point) :=
  if direction d ∈ F then none else some ((F ∪ deleted a d).image (recenter d))

/-- For every shared history-only controller and every n, radius at least n
reproduces the complete depth-n count exactly, provided the starting blockers
agree inside that light cone. No bound on the size of the complete blocker set
is required. This is a finite-depth theorem, not an interchange of limits. -/
theorem finite_horizon_exact (r n : ℕ) (hr : n ≤ r)
    (policy : List (Fin 3) → Fin 6) (h : List (Fin 3))
    (F G : Finset Point) (hFG : AgreeWithin n F G) :
    pathCount (geometricStep r) (fun h _ => policy h) n h F =
      pathCount completeStep (fun h _ => policy h) n h G := by
  induction n generalizing r h F G with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_congr rfl
      intro d _
      have hdir : gridRadius (direction d) ≤ n + 1 := by
        fin_cases d <;> norm_num [gridRadius, direction] <;> omega
      have heq := hFG (direction d) hdir
      by_cases hf : direction d ∈ F
      · have hg := heq.mp hf
        simp [geometricStep, completeStep, hf, hg]
      · have hg : direction d ∉ G := fun hg => hf (heq.mpr hg)
        have hchild : AgreeWithin n (memoryStep r F (policy h) d)
            ((G ∪ deleted (policy h) d).image (recenter d)) := by
          intro p hp
          change (p ∈ ((F ∪ deleted (policy h) d).image (recenter d)).filter
            (fun q => gridRadius q ≤ r)) ↔ _
          rw [Finset.mem_filter]
          have him := image_agrees n F G (policy h) d hFG p hp
          constructor
          · exact fun hh => him.mp hh.1
          · exact fun hh => ⟨him.mpr hh, hp.trans (by omega)⟩
        simpa only [geometricStep, completeStep, if_neg hf, if_neg hg,
          Option.elim_some] using
          ih r (by omega) (d :: h) (memoryStep r F (policy h) d)
            ((G ∪ deleted (policy h) d).image (recenter d)) hchild

#print axioms recenter_radius_bound
#print axioms memoryStep_agreeWithin
#print axioms finite_horizon_exact

end D5.S3.StatisticalMechanics.HardCore.MemoryLightCone
