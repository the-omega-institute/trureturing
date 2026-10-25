/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Proper nonempty cyclic intervals have a unique initial vertex and form disjoint deletion chains. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.Model

/-! Original-host mutual visibility and its finite reconfiguration geometry. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open scoped symmDiff

private def cyclicRank {m : ℕ} (i x : Fin m) : ℕ :=
  if i.val ≤ x.val then x.val - i.val else x.val + m - i.val

private theorem cyclicRank_lt {m : ℕ} (i x : Fin m) : cyclicRank i x < m := by
  unfold cyclicRank
  split <;> omega

private theorem cyclicRank_injective {m : ℕ} (i : Fin m) :
    Function.Injective (cyclicRank i) := by
  intro x y h
  unfold cyclicRank at h
  by_cases hx : i.val ≤ x.val <;> by_cases hy : i.val ≤ y.val <;>
    simp only [hx, hy, ite_true, ite_false] at h <;>
    apply Fin.ext <;> omega

private theorem cyclicRank_surjective {m : ℕ} (i : Fin m) {j : ℕ} (hj : j < m) :
    ∃ x : Fin m, cyclicRank i x = j := by
  by_cases h : i.val + j < m
  · refine ⟨⟨i.val + j, h⟩, ?_⟩
    simp [cyclicRank]
  · refine ⟨⟨i.val + j - m, by omega⟩, ?_⟩
    simp only [cyclicRank]
    split <;> omega

private def cyclicArc {m : ℕ} (i : Fin m) (k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun x => cyclicRank i x < k

private theorem mem_cyclicArc {m : ℕ} (i x : Fin m) (k : ℕ) :
    x ∈ cyclicArc i k ↔ cyclicRank i x < k := by simp [cyclicArc]

private theorem cyclicArc_card {m : ℕ} (i : Fin m) {k : ℕ} (hk : k ≤ m) :
    (cyclicArc i k).card = k := by
  have himage : (cyclicArc i k).image (cyclicRank i) = Finset.range k := by
    ext j
    constructor
    · rintro hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr ((mem_cyclicArc i x k).mp hx)
    · intro hj
      have hjk := Finset.mem_range.mp hj
      obtain ⟨x, hx⟩ := cyclicRank_surjective i (hjk.trans_le hk)
      exact Finset.mem_image.mpr ⟨x, (mem_cyclicArc i x k).mpr (hx ▸ hjk), hx⟩
  have hcard := congrArg Finset.card himage
  simpa [Finset.card_image_of_injective _ (cyclicRank_injective i)] using hcard

private theorem cyclicArc_full {m : ℕ} (i : Fin m) :
    cyclicArc i m = Finset.univ := by
  ext x
  simp [cyclicArc, cyclicRank_lt]

private theorem cyclicArc_zero {m : ℕ} (i : Fin m) : cyclicArc i 0 = ∅ := by
  simp [cyclicArc]

private theorem cyclicArc_initial {m : ℕ} (i : Fin m) {k : ℕ} (hk : 0 < k) :
    i ∈ cyclicArc i k := by simp [cyclicArc, cyclicRank, hk]

private def cyclicPred {m : ℕ} (x : Fin m) : Fin m :=
  if h : x.val = 0 then ⟨m - 1, by omega⟩ else ⟨x.val - 1, by omega⟩

private theorem cyclicArc_boundary {m : ℕ} (i x : Fin m) {k : ℕ}
    (hk : 0 < k) (hkm : k < m)
    (hx : x ∈ cyclicArc i k) (hp : cyclicPred x ∉ cyclicArc i k) : x = i := by
  have hx' := (mem_cyclicArc i x k).mp hx
  have hp' : k ≤ cyclicRank i (cyclicPred x) :=
    Nat.le_of_not_gt (fun h => hp ((mem_cyclicArc i _ k).mpr h))
  unfold cyclicRank at hx' hp'
  unfold cyclicPred at hp'
  by_cases hzero : x.val = 0 <;>
    simp only [hzero, dite_true, dite_false] at hp'
  all_goals
    split at hx' <;> split at hp' <;> apply Fin.ext <;> simp_all <;> omega

private theorem cyclicArc_pred_initial {m : ℕ} (i : Fin m) {k : ℕ} (hkm : k < m) :
    cyclicPred i ∉ cyclicArc i k := by
  intro hi
  have h := (mem_cyclicArc i _ k).mp hi
  unfold cyclicRank cyclicPred at h
  by_cases hz : i.val = 0 <;> simp only [hz, dite_true, dite_false] at h
  all_goals split at h <;> omega

private theorem cyclicArc_unique_start {m : ℕ} {i j : Fin m} {k l : ℕ}
    (hk : 0 < k) (hkm : k < m) (hl : 0 < l) (hlm : l < m)
    (he : cyclicArc i k = cyclicArc j l) : i = j := by
  apply cyclicArc_boundary j i hl hlm
  · rw [← he]; exact cyclicArc_initial i hk
  · rw [← he]; exact cyclicArc_pred_initial i hkm

private theorem cyclicArc_step {m : ℕ} (i : Fin m) {k : ℕ} (hk : k < m) :
    MixedMove (⊥ : SimpleGraph (Fin m)) (cyclicArc i k) (cyclicArc i (k + 1)) := by
  obtain ⟨x, hx⟩ := cyclicRank_surjective i hk
  have he : cyclicArc i k ∆ cyclicArc i (k + 1) = {x} := by
    ext y
    simp only [Finset.mem_symmDiff, mem_cyclicArc, Finset.mem_singleton]
    have hiff : cyclicRank i y = k ↔ y = x := by
      rw [← hx]
      exact ⟨fun h => cyclicRank_injective i h, congrArg (cyclicRank i)⟩
    omega
  refine ⟨?_, Or.inl (by rw [he, Finset.card_singleton])⟩
  intro h
  have h0 : (cyclicArc i k).card = (cyclicArc i (k + 1)).card := congrArg Finset.card h
  rw [cyclicArc_card i hk.le, cyclicArc_card i (by omega)] at h0
  omega

private theorem cyclicPred_injective {m : ℕ} : Function.Injective (@cyclicPred m) := by
  intro x y he
  have hv := congrArg Fin.val he
  unfold cyclicPred at hv
  by_cases hx : x.val = 0 <;> by_cases hy : y.val = 0 <;>
    simp only [hx, hy, dite_true, dite_false] at hv <;> apply Fin.ext <;> omega

private theorem cyclicArc_coatom {m : ℕ} (i : Fin m) :
    cyclicArc i (m - 1) = Finset.univ.erase (cyclicPred i) := by
  have hm : 0 < m := by omega
  have hsub : cyclicArc i (m - 1) ⊆ Finset.univ.erase (cyclicPred i) := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    subst x
    exact cyclicArc_pred_initial i (by omega) hx
  apply Finset.eq_of_subset_of_card_le hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, cyclicArc_card i (by omega : m - 1 ≤ m)]
  exact le_rfl

private theorem cyclicArc_mono {m : ℕ} (i : Fin m) {k l : ℕ} (h : k ≤ l) :
    cyclicArc i k ⊆ cyclicArc i l := by
  intro x hx
  exact (mem_cyclicArc i x l).mpr (lt_of_lt_of_le ((mem_cyclicArc i x k).mp hx) h)

private theorem cyclicArc_extend {m : ℕ} (i : Fin m) {k : ℕ} (hk : k < m) :
    ∃ x, x ∉ cyclicArc i k ∧ cyclicArc i (k + 1) = insert x (cyclicArc i k) := by
  obtain ⟨x, hx⟩ := cyclicRank_surjective i hk
  refine ⟨x, ?_, ?_⟩
  · simp [mem_cyclicArc, hx]
  · ext y
    simp only [mem_cyclicArc, Finset.mem_insert]
    have he : y = x ↔ cyclicRank i y = k := by
      rw [← hx]
      exact ⟨congrArg (cyclicRank i), fun h => cyclicRank_injective i h⟩
    omega

private def mappedArc {V : Type*} {m : ℕ} (e : Fin m ↪ V) (i : Fin m) (k : ℕ) :
    Finset V := (cyclicArc i k).map e

private theorem mappedArc_card {V : Type*} {m : ℕ} (e : Fin m ↪ V) (i : Fin m)
    {k : ℕ} (hk : k ≤ m) : (mappedArc e i k).card = k := by
  simp only [mappedArc, Finset.card_map, cyclicArc_card i hk]

private theorem mappedArc_unique_start {V : Type*} {m : ℕ} (e : Fin m ↪ V)
    {i j : Fin m} {k l : ℕ} (hk : 0 < k) (hkm : k < m) (hl : 0 < l) (hlm : l < m)
    (he : mappedArc e i k = mappedArc e j l) : i = j :=
  cyclicArc_unique_start hk hkm hl hlm (Finset.map_injective e he)

private theorem mappedArc_step {V : Type*} [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (i : Fin m) {k : ℕ} (hk : k < m) :
    MixedMove H (mappedArc e i k) (mappedArc e i (k + 1)) := by
  obtain ⟨x, hx, he⟩ := cyclicArc_extend i hk
  have hn : e x ∉ mappedArc e i k := by simpa [mappedArc] using hx
  have hm := mixedMove_insert H (mappedArc e i k) hn
  simpa only [mappedArc, he, Finset.map_insert] using hm

end D5.S3.Combinatorics.Graph.MutualVisibility
