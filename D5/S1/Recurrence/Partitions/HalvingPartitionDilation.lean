/- GID: D5/S1/Recurrence/Partitions/HalvingPartitionDilation
   generality: I
   mirror-B: D5/B/S1/Recurrence/Partitions/HalvingPartitionDilation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Even dilation preserves the actual halving-list count by removing its forced first part. -/

import D5.S1.Recurrence.Partitions.HalvingPartitionProfile

/-! Alekseyev (2026), Lemma 2, with literal lists and all repeated ones retained. -/

namespace D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity

/-- At positive even total, the first part is forced and its deletion is invertible. -/
def evenSourceEquiv (n : ℕ) (hn : 0 < n) : SourceLists n ≃ SourceLists (2 * n) where
  toFun p := ⟨n :: p.val, by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hn
      · exact p.prop.1 x hx
    · simp [p.prop.2.1, two_mul]
    · exact ⟨Or.inl (by omega), p.prop.2.2⟩⟩
  invFun p := ⟨p.val.tail, by
    have hhead : ∃ xs, p.val = n :: xs := by
      cases he : p.val with
      | nil => have hs := p.prop.2.1; rw [he] at hs; simp only [List.sum_nil] at hs; omega
      | cons x xs =>
        have hf := p.prop.2.2
        rw [he] at hf
        have hx : x = n := by rcases hf.1 with h | h <;> omega
        exact ⟨xs, by rw [hx]⟩
    obtain ⟨xs, hxs⟩ := hhead
    have hs := p.prop.2.1
    have hf := p.prop.2.2
    rw [hxs] at hs hf ⊢
    simp only [List.tail_cons]
    refine ⟨fun x hx => p.prop.1 x (by simp [hxs, hx]), ?_, hf.2⟩
    simp only [List.sum_cons] at hs
    simpa only [List.tail_cons] using (show xs.sum = n by omega)⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by
    apply Subtype.ext
    cases he : p.val with
    | nil => have hs := p.prop.2.1; rw [he] at hs; simp only [List.sum_nil] at hs; omega
    | cons x xs =>
      have hf := p.prop.2.2
      rw [he] at hf
      have hx : x = n := by rcases hf.1 with h | h <;> omega
      simpa only [he, List.tail_cons] using congrArg (fun k => k :: xs) hx.symm

/-- Count invariance is transported through the actual forced-part bijection. -/
theorem count_even (n : ℕ) : count (2 * n) = count n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Nat.card_congr (evenSourceEquiv n (by omega)).symm

/-- Iterated even dilation, used for the manuscript's deficit family. -/
theorem count_even_dilation (n v : ℕ) : count (2 ^ v * n) = count n := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ, show 2 ^ v * 2 * n = 2 * (2 ^ v * n) by ring, count_even, ih]

end D5.S1.Recurrence.Partitions.HalvingPartitionNonregularity
