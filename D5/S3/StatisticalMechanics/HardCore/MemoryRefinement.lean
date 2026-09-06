/- GID: D5/S3/StatisticalMechanics/HardCore/MemoryRefinement
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/MemoryRefinement
   mirror-E: none(waiver:symbolic-geometric-simulation)
   anchors: []
   digest: Larger retained geometry dominates coarse paths under synchronized controllers. -/

import D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.MemoryRefinement

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

/-- The geometric memory transition itself, before any finite presentation. -/
def geometricStep (r : ℕ) (F : Finset Point) (a : Fin 6) (d : Fin 3) :
    Option (Finset Point) :=
  if direction d ∈ F then none else some (memoryStep r F a d)

/-- Increasing both the retained radius and the recorded blocker set preserves
blocker inclusion, for the same ordering and chosen direction. -/
theorem memoryStep_mono {r R : ℕ} (hr : r ≤ R) {F G : Finset Point}
    (hFG : F ⊆ G) (a : Fin 6) (d : Fin 3) :
    memoryStep r F a d ⊆ memoryStep R G a d := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp, hb⟩
  rcases Finset.mem_image.mp hp with ⟨q, hq, heq⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨q, ?_, heq⟩, hb.trans hr⟩
  rcases Finset.mem_union.mp hq with hqF | hqK
  · exact Finset.mem_union.mpr (Or.inl (hFG hqF))
  · exact Finset.mem_union.mpr (Or.inr hqK)

/-- For a common history-based ordering, larger memory has no more paths at
any depth. Independent state-dependent controllers are not covered by this claim. -/
theorem history_count_antitone (r R : ℕ) (hr : r ≤ R)
    (policy : List (Fin 3) → Fin 6) (n : ℕ) (h : List (Fin 3))
    (F G : Finset Point) (hFG : F ⊆ G) :
    pathCount (geometricStep R) (fun h _ => policy h) n h G ≤
      pathCount (geometricStep r) (fun h _ => policy h) n h F := by
  induction n generalizing h F G with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_le_sum
      intro d _
      by_cases hg : direction d ∈ G
      · simp [geometricStep, hg]
      · have hf : direction d ∉ F := fun hf => hg (hFG hf)
        simpa only [geometricStep, if_neg hg, if_neg hf, Option.elim_some] using
          ih (d :: h) (memoryStep r F (policy h) d)
            (memoryStep R G (policy h) d) (memoryStep_mono hr hFG (policy h) d)

/-- Keep a coarse controller's actual memory alongside a refined memory.
Refined blockers decide child availability; both memories receive the same action.
The coarse memory is not reconstructed by projecting the fine memory. -/
def coupledStep (r R : ℕ) (s : Finset Point × Finset Point)
    (a : Fin 6) (d : Fin 3) : Option (Finset Point × Finset Point) :=
  if direction d ∈ s.2 then none
  else some (memoryStep r s.1 a d, memoryStep R s.2 a d)

/-- Explicit controller transport. Every state- and history-dependent coarse
controller can be run on the coupled refinement without increasing any path count. -/
theorem coupled_count_le_coarse (r R : ℕ) (hr : r ≤ R)
    (policy : List (Fin 3) → Finset Point → Fin 6)
    (n : ℕ) (h : List (Fin 3)) (F G : Finset Point) (hFG : F ⊆ G) :
    pathCount (coupledStep r R) (fun h s => policy h s.1) n h (F, G) ≤
      pathCount (geometricStep r) policy n h F := by
  induction n generalizing h F G with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_le_sum
      intro d _
      by_cases hg : direction d ∈ G
      · simp [coupledStep, hg]
      · have hf : direction d ∉ F := fun hf => hg (hFG hf)
        simpa only [coupledStep, geometricStep, if_neg hg, if_neg hf,
          Option.elim_some] using
          ih (d :: h) (memoryStep r F (policy h F) d)
            (memoryStep R G (policy h F) d) (memoryStep_mono hr hFG (policy h F) d)

/-- A finite representation with exact direction-preserving transitions has
exactly the same fixed-order path counts as its actual geometric masks.
Only the selected order must be closed; unused actions need no extra states. -/
theorem fixed_presentation_count {State : Type*}
    (step : State → Fin 6 → Fin 3 → Option State) (mask : State → Finset Point)
    (r : ℕ) (a : Fin 6)
    (hstep : ∀ i d, (step i a d).map mask = geometricStep r (mask i) a d)
    (n : ℕ) (h : List (Fin 3)) (i : State) :
    pathCount step (fun _ _ => a) n h i =
      pathCount (geometricStep r) (fun _ _ => a) n h (mask i) := by
  induction n generalizing h i with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_congr rfl
      intro d _
      have ht := hstep i d
      cases hs : step i a d with
      | none =>
          have he : geometricStep r (mask i) a d = none := by simpa [hs] using ht.symm
          simp [hs, he]
      | some j =>
          have he : geometricStep r (mask i) a d = some (mask j) := by
            simpa [hs] using ht.symm
          simpa [hs, he] using ih (d :: h) j

#print axioms memoryStep_mono
#print axioms history_count_antitone
#print axioms coupled_count_le_coarse
#print axioms fixed_presentation_count

end D5.S3.StatisticalMechanics.HardCore.MemoryRefinement
