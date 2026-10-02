/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Bounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Bounds
   mirror-E: none(waiver:rotation-block-inversion-bounds)
   anchors: []
   utility: none
   digest: Rotation blocks tighten exactly the bounds on entries joined to their predecessors. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Rotation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Bounds

theorem rotated_suffix_bounds_iff (blocks : List (List ℕ)) (base : ℕ)
    (hnonempty : ∀ block ∈ blocks, block ≠ [])
    (hsorted : blocks.flatten.Pairwise (· < ·)) :
    (∀ index < (blocks.flatMap (fun block => block.rotate 1)).length,
      (blocks.flatMap (fun block => block.rotate 1)).getD index 0 ≤ base + index) ↔
    (∀ index < blocks.flatten.length, blocks.flatten.getD index 0 ≤ base + index) ∧
    (∀ blockIndex < blocks.length, ∀ index < (blocks.getD blockIndex []).tail.length,
      (blocks.getD blockIndex []).tail.getD index 0 ≤
        base + (blocks.take blockIndex).flatten.length + index) := by
  have happend (first second : List ℕ) (offset : ℕ) :
      (∀ index < (first ++ second).length,
        (first ++ second).getD index 0 ≤ offset + index) ↔
      (∀ index < first.length, first.getD index 0 ≤ offset + index) ∧
      (∀ index < second.length, second.getD index 0 ≤ offset + first.length + index) := by
    constructor
    · intro hbound
      constructor
      · intro index hindex
        have := hbound index (by simp; omega)
        rwa [List.getD_append _ _ _ _ hindex] at this
      · intro index hindex
        have := hbound (first.length + index) (by simp; omega)
        rw [List.getD_append_right first second 0 (first.length + index) (by omega)] at this
        simpa [Nat.add_assoc] using this
    · rintro ⟨hfirst, hsecond⟩ index hindex
      by_cases hleft : index < first.length
      · rw [List.getD_append _ _ _ _ hleft]
        exact hfirst index hleft
      · rw [List.getD_append_right _ _ _ _ (by omega)]
        have hsecond' := hsecond (index - first.length) (by simp at hindex; omega)
        omega
  have hblock (minimum : ℕ) (rest : List ℕ) (offset : ℕ)
      (hs : (minimum :: rest).Pairwise (· < ·)) :
      (∀ index < (rest ++ [minimum]).length,
        (rest ++ [minimum]).getD index 0 ≤ offset + index) ↔
      (∀ index < (minimum :: rest).length,
        (minimum :: rest).getD index 0 ≤ offset + index) ∧
      (∀ index < rest.length, rest.getD index 0 ≤ offset + index) := by
    rw [happend]
    constructor
    · rintro ⟨hrest, hlast⟩
      have hminimum : minimum ≤ offset := by
        cases rest with
        | nil => simpa using hlast 0 (by simp)
        | cons next tail =>
          have hnext := hrest 0 (by simp)
          have hlt := (List.pairwise_cons.mp hs).1 next (by simp)
          simp only [List.getD_cons_zero, Nat.add_zero] at hnext
          omega
      refine ⟨?_, hrest⟩
      intro index hindex
      cases index with
      | zero => simpa using hminimum
      | succ index =>
        have := hrest index (by simpa using hindex)
        simp only [List.getD_cons_succ]
        omega
    · rintro ⟨hsortedBound, hrest⟩
      refine ⟨hrest, ?_⟩
      intro index hindex
      have hzero : index = 0 := by simpa using hindex
      subst index
      have := hsortedBound 0 (by simp)
      simp only [List.getD_cons_zero, Nat.add_zero] at this
      simpa using (show minimum ≤ offset + rest.length from by omega)
  induction blocks generalizing base with
  | nil => simp
  | cons block blocks ih =>
    have hbne := hnonempty block (by simp)
    have htailne : ∀ piece ∈ blocks, piece ≠ [] := by
      intro piece hpiece
      exact hnonempty piece (by simp [hpiece])
    have hs : block.Pairwise (· < ·) ∧ blocks.flatten.Pairwise (· < ·) := by
      have := List.pairwise_append.mp hsorted
      exact ⟨this.1, this.2.1⟩
    cases block with
    | nil => exact (hbne rfl).elim
    | cons minimum rest =>
      have hjoined :
          (∀ blockIndex < ((minimum :: rest) :: blocks).length,
            ∀ index < (((minimum :: rest) :: blocks).getD blockIndex []).tail.length,
              (((minimum :: rest) :: blocks).getD blockIndex []).tail.getD index 0 ≤
                base + (((minimum :: rest) :: blocks).take blockIndex).flatten.length +
                  index) ↔
          (∀ index < rest.length, rest.getD index 0 ≤ base + index) ∧
          (∀ blockIndex < blocks.length, ∀ index < (blocks.getD blockIndex []).tail.length,
            (blocks.getD blockIndex []).tail.getD index 0 ≤
              (base + (minimum :: rest).length) + (blocks.take blockIndex).flatten.length +
                index) := by
        constructor
        · intro hjoined
          constructor
          · intro index hindex
            simpa using hjoined 0 (by simp) index (by simpa using hindex)
          · intro blockIndex hblockIndex index hindex
            simpa [List.take_succ_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using hjoined (blockIndex + 1) (by simp; omega) index (by simpa using hindex)
        · rintro ⟨hhead, htail⟩ blockIndex hblockIndex index hindex
          cases blockIndex with
          | zero => simpa using hhead index (by simpa using hindex)
          | succ blockIndex =>
            simpa [List.take_succ_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using htail blockIndex (by simpa using hblockIndex) index
                (by simpa using hindex)
      simp only [List.flatMap_cons, List.rotate_cons_succ, List.rotate_zero,
        List.flatten_cons]
      rw [happend, hblock minimum rest base hs.1]
      rw [show (rest ++ [minimum]).length = (minimum :: rest).length by simp]
      have htail := ih (base + (minimum :: rest).length) htailne hs.2
      rw [happend, hjoined]
      constructor
      · rintro ⟨⟨hhead, hjhead⟩, hactualTail⟩
        obtain ⟨hsortedTail, hjoinedTail⟩ := htail.mp hactualTail
        exact ⟨⟨hhead, hsortedTail⟩, hjhead, hjoinedTail⟩
      · rintro ⟨⟨hhead, hsortedTail⟩, hjhead, hjoinedTail⟩
        exact ⟨⟨hhead, hjhead⟩, htail.mpr ⟨hsortedTail, hjoinedTail⟩⟩

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Bounds
