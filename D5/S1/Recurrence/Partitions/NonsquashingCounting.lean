/- GID: D5/S1/Recurrence/Partitions/NonsquashingCounting
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/NonsquashingCounting
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Counting distinct non-squashing partitions by removing the largest part. -/

import Mathlib

namespace D5.S1.Recurrence.Partitions.NonsquashingCounting
open Finset

/-- Distinct positive parts with each part at least the sum of all smaller parts. -/
def nonsquashingDistinctPartitions (n : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 n).powerset).filter fun s =>
    s.sum id = n ∧ ∀ p ∈ s, (s.filter (fun q => q < p)).sum id ≤ p

private theorem mem_parts {s : Finset ℕ} {n : ℕ} :
    s ∈ nonsquashingDistinctPartitions n ↔
      (∀ p ∈ s, 0 < p) ∧ s.sum id = n ∧
      ∀ p ∈ s, (s.filter (fun q => q < p)).sum id ≤ p := by
  simp only [nonsquashingDistinctPartitions, mem_filter, mem_powerset]
  constructor
  · rintro ⟨hb, hn, hns⟩
    exact ⟨fun p hp => (mem_Icc.mp (hb hp)).1, hn, hns⟩
  · rintro ⟨hp, hn, hns⟩
    refine ⟨?_, hn, hns⟩
    intro p hps
    exact mem_Icc.mpr ⟨hp p hps, hn ▸ single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hps⟩

private theorem part_le_sum {s : Finset ℕ} {p : ℕ} (hp : p ∈ s) : p ≤ s.sum id :=
  single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hp

private theorem subset_parts {s t : Finset ℕ} {n : ℕ}
    (hs : s ∈ nonsquashingDistinctPartitions n) (ht : t ⊆ s) :
    t ∈ nonsquashingDistinctPartitions (t.sum id) := by
  obtain ⟨hpos, _, hns⟩ := mem_parts.mp hs
  apply mem_parts.mpr
  refine ⟨fun p hp => hpos p (ht hp), rfl, ?_⟩
  intro p hp
  exact (sum_le_sum_of_subset (filter_subset_filter _ ht)).trans (hns p (ht hp))

private theorem insert_parts {s : Finset ℕ} {k p : ℕ}
    (hs : s ∈ nonsquashingDistinctPartitions k) (hp : 0 < p)
    (hk : k ≤ p) (hne : p ∉ s) :
    insert p s ∈ nonsquashingDistinctPartitions (p + k) := by
  obtain ⟨hpos, hsum, hns⟩ := mem_parts.mp hs
  have hlt : ∀ q ∈ s, q < p := by
    intro q hq
    have hqk := part_le_sum hq
    rw [hsum] at hqk
    exact lt_of_le_of_ne (hqk.trans hk) (by rintro rfl; exact hne hq)
  apply mem_parts.mpr
  refine ⟨?_, by rw [sum_insert hne, hsum]; rfl, ?_⟩
  · intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hpos q hq
  · intro q hq
    rcases mem_insert.mp hq with heq | hqs
    · subst q
      have he : (insert p s).filter (fun q => q < p) = s := by
        ext q
        simp only [mem_filter, mem_insert]
        exact ⟨fun h => h.1.resolve_left (by omega), fun h => ⟨Or.inr h, hlt q h⟩⟩
      rw [he, hsum]
      exact hk
    · have he : (insert p s).filter (fun r => r < q) = s.filter (fun r => r < q) := by
        ext r
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨rfl | hr, hrq⟩
          · have := hlt q hqs
            omega
          · exact ⟨hr, hrq⟩
        · rintro ⟨hr, hrq⟩
          exact ⟨Or.inr hr, hrq⟩
      rw [he]
      exact hns q hqs

private def cumulative (m : ℕ) : Finset (Finset ℕ) :=
  (range (m + 1)).biUnion nonsquashingDistinctPartitions

private theorem mem_cumulative {s : Finset ℕ} {m : ℕ} :
    s ∈ cumulative m ↔
      s ∈ nonsquashingDistinctPartitions (s.sum id) ∧ s.sum id ≤ m := by
  simp only [cumulative, mem_biUnion, mem_range]
  constructor
  · rintro ⟨k, hk, hs⟩
    have he := (mem_parts.mp hs).2.1
    exact ⟨he.symm ▸ hs, by omega⟩
  · rintro ⟨hs, hm⟩
    exact ⟨s.sum id, by omega, hs⟩

private theorem card_cumulative (m : ℕ) :
    (cumulative m).card = ∑ k ∈ range (m + 1), (nonsquashingDistinctPartitions k).card := by
  apply card_biUnion
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro s hsi hsj
  exact hij ((mem_parts.mp hsi).2.1.symm.trans (mem_parts.mp hsj).2.1)

private theorem erase_max_parts {s : Finset ℕ} {n : ℕ}
    (hs : s ∈ nonsquashingDistinctPartitions n) (hn : 0 < n) :
    ∃ t ∈ cumulative (n / 2), n - t.sum id ∉ t ∧ insert (n - t.sum id) t = s := by
  have hne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := not_nonempty_iff_eq_empty.mp h
    have hsum := (mem_parts.mp hs).2.1
    simp [he] at hsum
    omega
  let p := s.max' hne
  have hp : p ∈ s := s.max'_mem hne
  let t := s.erase p
  have hfilter : s.filter (fun q => q < p) = t := by
    ext q
    simp only [mem_filter, t, mem_erase]
    constructor
    · rintro ⟨hq, hqp⟩
      exact ⟨by omega, hq⟩
    · rintro ⟨hqp, hq⟩
      exact ⟨hq, lt_of_le_of_ne (s.le_max' q hq) hqp⟩
  have ht_le : t.sum id ≤ p := by
    rw [← hfilter]
    exact (mem_parts.mp hs).2.2 p hp
  have hsum : t.sum id + p = n := by
    change (s.erase p).sum id + p = n
    exact (sum_erase_add s id hp).trans (mem_parts.mp hs).2.1
  have hep : n - t.sum id = p := by omega
  refine ⟨t, mem_cumulative.mpr ⟨subset_parts hs (erase_subset _ _), by omega⟩, ?_, ?_⟩
  · rw [hep]
    exact notMem_erase _ _
  · rw [hep]
    exact insert_erase hp

private theorem insert_injective (n : ℕ) {s t : Finset ℕ}
    (hs : s ∈ cumulative (n / 2)) (ht : t ∈ cumulative (n / 2))
    (hsn : n - s.sum id ∉ s) (htn : n - t.sum id ∉ t)
    (he : insert (n - s.sum id) s = insert (n - t.sum id) t) : s = t := by
  have hsl := (mem_cumulative.mp hs).2
  have htl := (mem_cumulative.mp ht).2
  have h1 : n - s.sum id ≤ n - t.sum id := by
    have hmem : n - s.sum id ∈ insert (n - t.sum id) t := by
      rw [← he]
      exact mem_insert_self _ _
    rcases mem_insert.mp hmem with h | h
    · omega
    · have := part_le_sum h
      omega
  have h2 : n - t.sum id ≤ n - s.sum id := by
    have hmem : n - t.sum id ∈ insert (n - s.sum id) s := by
      rw [he]
      exact mem_insert_self _ _
    rcases mem_insert.mp hmem with h | h
    · omega
    · have := part_le_sum h
      omega
  have hep : n - s.sum id = n - t.sum id := by omega
  have he' := congrArg (fun u => u.erase (n - s.sum id)) he
  rw [erase_insert hsn, hep, erase_insert htn] at he'
  exact he'

private theorem card_extension (n : ℕ) (hn : 0 < n) :
    (nonsquashingDistinctPartitions n).card =
      ((cumulative (n / 2)).filter fun s => n - s.sum id ∉ s).card := by
  symm
  apply card_bij (fun s _ => insert (n - s.sum id) s)
  · intro s hs
    obtain ⟨hc, hne⟩ := mem_filter.mp hs
    obtain ⟨hp, hsum⟩ := mem_cumulative.mp hc
    have h := insert_parts hp (by omega : 0 < n - s.sum id) (by omega) hne
    simpa only [Nat.sub_add_cancel (by omega : s.sum id ≤ n)] using h
  · intro s hs t ht he
    exact insert_injective n (mem_filter.mp hs).1 (mem_filter.mp ht).1
      (mem_filter.mp hs).2 (mem_filter.mp ht).2 he
  · intro s hs
    obtain ⟨t, ht, hne, he⟩ := erase_max_parts hs hn
    exact ⟨t, mem_filter.mpr ⟨ht, hne⟩, he⟩

private theorem odd_sum (m : ℕ) :
    (nonsquashingDistinctPartitions (2 * m + 1)).card =
      ∑ k ∈ range (m + 1), (nonsquashingDistinctPartitions k).card := by
  rw [card_extension _ (by omega), show (2*m+1)/2=m by omega]
  rw [filter_true_of_mem, card_cumulative]
  intro s hs hmem
  have hsum := (mem_cumulative.mp hs).2
  have := part_le_sum hmem
  omega

private theorem singleton_mem (m : ℕ) (hm : 0 < m) :
    {m} ∈ nonsquashingDistinctPartitions m := by
  apply mem_parts.mpr
  simp [hm, filter_singleton]

private theorem even_exception (m : ℕ) {s : Finset ℕ}
    (hs : s ∈ cumulative m) : 2*m - s.sum id ∈ s ↔ s = {m} := by
  obtain ⟨hp, hsum⟩ := mem_cumulative.mp hs
  obtain ⟨hpos, _, _⟩ := mem_parts.mp hp
  constructor
  · intro he
    have hle := part_le_sum he
    have hsum_eq : s.sum id = m := by omega
    have hpart : 2*m-s.sum id = m := by omega
    rw [hpart] at he
    have herase : (s.erase m).sum id = 0 := by
      have hh := sum_erase_add s id he
      change (s.erase m).sum id + m = s.sum id at hh
      omega
    ext q
    simp only [mem_singleton]
    constructor
    · intro hq
      by_contra hqm
      have hq' : q ∈ s.erase m := mem_erase.mpr ⟨hqm, hq⟩
      have hle' := part_le_sum hq'
      have hpos' := hpos q hq
      omega
    · rintro rfl
      exact he
  · rintro rfl
    simp only [sum_singleton, id_eq, mem_singleton]
    omega

private theorem even_sum (m : ℕ) (hm : 0 < m) :
    (nonsquashingDistinctPartitions (2 * m)).card + 1 =
      ∑ k ∈ range (m + 1), (nonsquashingDistinctPartitions k).card := by
  rw [card_extension _ (by omega), show 2*m/2=m by omega]
  have he : (cumulative m).filter (fun s => 2*m-s.sum id ∉ s) =
      (cumulative m).erase {m} := by
    ext s
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hs, hnot⟩
      exact ⟨fun he => hnot ((even_exception m hs).mpr he), hs⟩
    · rintro ⟨hne, hs⟩
      exact ⟨hs, fun hmem => hne ((even_exception m hs).mp hmem)⟩
  rw [he, card_erase_add_one, card_cumulative]
  apply mem_cumulative.mpr
  simpa only [sum_singleton, id_eq] using And.intro (singleton_mem m hm) (le_refl m)

/-- The odd-index increment, with the necessary positive half-index. -/
theorem count_odd (m : ℕ) (hm : 0 < m) :
    (nonsquashingDistinctPartitions (2*m+1)).card =
      (nonsquashingDistinctPartitions (2*m)).card + 1 := by
  rw [odd_sum, even_sum m hm]

/-- Successive positive even indices differ by the count at their half-index. -/
theorem count_even_step (m : ℕ) (hm : 0 < m) :
    (nonsquashingDistinctPartitions (2*(m+1))).card =
      (nonsquashingDistinctPartitions (2*m)).card +
        (nonsquashingDistinctPartitions (m+1)).card := by
  have h1 := even_sum m hm
  have h2 := even_sum (m+1) (by omega)
  rw [sum_range_succ] at h2
  omega

#print axioms count_odd
#print axioms count_even_step
end D5.S1.Recurrence.Partitions.NonsquashingCounting
