/- GID: D5/S3/StatisticalMechanics/HardCore/MemoryBlockBounds
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/MemoryBlockBounds
   mirror-E: none(waiver:symbolic-uniform-block-bound)
   anchors: []
   digest: Exact complete prefixes give uniform all-depth bounds for sufficiently large memories. -/

import D5.S3.StatisticalMechanics.HardCore.MemoryLightCone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.MemoryBlockBounds

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential
open D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
open D5.S3.StatisticalMechanics.HardCore.MemoryRefinement
open D5.S3.StatisticalMechanics.HardCore.MemoryLightCone

/-- Complete blocker accumulation has no more paths than truncated memory,
under a common history-based ordering and inclusion of the starting blockers. -/
theorem complete_count_le_memory (r : ℕ) (policy : List (Fin 3) → Fin 6)
    (n : ℕ) (h : List (Fin 3)) (F G : Finset Point) (hFG : F ⊆ G) :
    pathCount completeStep (fun h _ => policy h) n h G ≤
      pathCount (geometricStep r) (fun h _ => policy h) n h F := by
  induction n generalizing h F G with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_le_sum
      intro d _
      by_cases hg : direction d ∈ G
      · simp [completeStep, hg]
      · have hf : direction d ∉ F := fun hf => hg (hFG hf)
        have hc : memoryStep r F (policy h) d ⊆
            (G ∪ deleted (policy h) d).image (recenter d) := by
          intro p hp
          rcases Finset.mem_image.mp (Finset.mem_filter.mp hp).1 with ⟨q, hq, heq⟩
          refine Finset.mem_image.mpr ⟨q, ?_, heq⟩
          rcases Finset.mem_union.mp hq with hqF | hqK
          · exact Finset.mem_union.mpr (Or.inl (hFG hqF))
          · exact Finset.mem_union.mpr (Or.inr hqK)
        simpa only [completeStep, geometricStep, if_neg hg, if_neg hf,
          Option.elim_some] using
          ih (d :: h) (memoryStep r F (policy h) d)
            ((G ∪ deleted (policy h) d).image (recenter d)) hc

private theorem fixed_history (r n : ℕ) (a : Fin 6)
    (h h' : List (Fin 3)) (F : Finset Point) :
    pathCount (geometricStep r) (fun _ _ => a) n h F =
      pathCount (geometricStep r) (fun _ _ => a) n h' F := by
  induction n generalizing h h' F with
  | zero => simp [pathCount]
  | succ n ih =>
      simp only [pathCount]
      apply Finset.sum_congr rfl
      intro d _
      cases hs : geometricStep r F a d with
      | none => simp
      | some G => simpa using ih (d :: h) (d :: h') G

private theorem parent_retained (r : ℕ) (hr : 1 ≤ r)
    (F : Finset Point) (a : Fin 6) (d : Fin 3) :
    (-1, 0) ∈ memoryStep r F a d := by
  apply Finset.mem_filter.mpr
  constructor
  · refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
    · simp [deleted]
    · fin_cases d <;> norm_num [recenter]
  · simpa using hr

private theorem child_has_parent (r : ℕ) (hr : 1 ≤ r)
    (F G : Finset Point) (a : Fin 6) (d : Fin 3)
    (hs : geometricStep r F a d = some G) : (-1, 0) ∈ G := by
  unfold geometricStep at hs
  split_ifs at hs with hd
  · simp at hs
  · have he := Option.some.inj hs
    rw [← he]
    exact parent_retained r hr F a d

private theorem count_le_three_pow (r n : ℕ) (a : Fin 6)
    (h : List (Fin 3)) (F : Finset Point) :
    pathCount (geometricStep r) (fun _ _ => a) n h F ≤ 3 ^ n := by
  induction n generalizing h F with
  | zero => simp [pathCount]
  | succ n ih =>
      calc
        _ ≤ ∑ _ : Fin 3, 3 ^ n := by
          simp only [pathCount]
          apply Finset.sum_le_sum
          intro d _
          cases hs : geometricStep r F a d with
          | none => simp
          | some G => simpa using ih (d :: h) G
        _ = 3 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

private theorem append_bound (r : ℕ) (hr : 1 ≤ r) (a : Fin 6)
    (m M : ℕ)
    (hM : ∀ h F, (-1, 0) ∈ F →
      pathCount (geometricStep r) (fun _ _ => a) m h F ≤ M)
    (n : ℕ) (h : List (Fin 3)) (F : Finset Point) (hF : (-1, 0) ∈ F) :
    pathCount (geometricStep r) (fun _ _ => a) (n + m) h F ≤
      M * pathCount (geometricStep r) (fun _ _ => a) n h F := by
  induction n generalizing h F with
  | zero => simpa [pathCount] using hM h F hF
  | succ n ih =>
      simp only [Nat.succ_add, pathCount, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d _
      cases hs : geometricStep r F a d with
      | none => simp
      | some G =>
          simpa using ih (d :: h) G (child_has_parent r hr F G a d hs)

private theorem prefix_le_complete (r k : ℕ) (hk : k ≤ r) (a : Fin 6)
    (h : List (Fin 3)) (F : Finset Point) (hF : (-1, 0) ∈ F) :
    pathCount (geometricStep r) (fun _ _ => a) k h F ≤
      pathCount completeStep (fun _ _ => a) k [] {(-1, 0)} := by
  have hsub : {(-1, 0)} ⊆ F := by
    intro p hp
    have he := Finset.mem_singleton.mp hp
    subst p
    exact hF
  calc
    _ ≤ pathCount (geometricStep r) (fun _ _ => a) k h {(-1, 0)} :=
      history_count_antitone r r le_rfl (fun _ => a) k h {(-1, 0)} F hsub
    _ = pathCount (geometricStep r) (fun _ _ => a) k [] {(-1, 0)} :=
      fixed_history r k a h [] {(-1, 0)}
    _ = _ := finite_horizon_exact r k hk (fun _ => a) []
      {(-1, 0)} {(-1, 0)} (by intro p hp; rfl)

/-- A complete depth-k prefix supplies a uniform bound at every later depth
for every retention radius r at least k. The same relative ordering is fixed
throughout. The initial blocked set is arbitrary provided it contains the parent.
This explicit block estimate supplies the missing uniformity needed for the
paper-level completeness of the fixed-order memory hierarchy. -/
theorem fixed_order_block_bound (r k : ℕ) (hr : 1 ≤ r) (hk : k ≤ r)
    (a : Fin 6) (q s : ℕ) (h : List (Fin 3)) (F : Finset Point)
    (hF : (-1, 0) ∈ F) :
    pathCount (geometricStep r) (fun _ _ => a) (q * k + s) h F ≤
      (pathCount completeStep (fun _ _ => a) k [] {(-1, 0)}) ^ q * 3 ^ s := by
  let C := pathCount completeStep (fun _ _ => a) k [] {(-1, 0)}
  change _ ≤ C ^ q * 3 ^ s
  induction q generalizing h F with
  | zero => simpa using count_le_three_pow r s a h F
  | succ q ih =>
      calc
        _ = pathCount (geometricStep r) (fun _ _ => a) (k + (q * k + s)) h F := by
          congr 1 <;> ring
        _ ≤ (C ^ q * 3 ^ s) *
            pathCount (geometricStep r) (fun _ _ => a) k h F :=
          append_bound r hr a (q * k + s) (C ^ q * 3 ^ s)
            (fun h G hG => ih h G hG) k h F hF
        _ ≤ (C ^ q * 3 ^ s) * C := Nat.mul_le_mul_left _
          (prefix_le_complete r k hk a h F hF)
        _ = C ^ (q + 1) * 3 ^ s := by rw [pow_succ]; ring

#print axioms complete_count_le_memory
#print axioms fixed_order_block_bound

end D5.S3.StatisticalMechanics.HardCore.MemoryBlockBounds
