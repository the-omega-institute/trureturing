/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicParents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicParents
   mirror-E: none(waiver:maximum-parent-bijection)
   anchors: []
   utility: none
   digest: Deleting the unique maximum inverts insertion at an active gap for every class. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicParents

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion

set_option maxHeartbeats 1200000 in
theorem maximum_insertion_bijection (n : ℕ) (patterns : List (List ℕ)) :
    Function.Bijective (fun entry : {entry : List ℕ × ℕ //
      entry.1 ∈ avoiders n patterns ∧ entry.2 ≤ entry.1.length ∧
        entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns} =>
      (⟨entry.val.1.insertIdx entry.val.2 (n + 1), entry.property.2.2⟩ :
        avoiders (n + 1) patterns)) := by
  constructor
  · intro first second heq
    have hchild : first.val.1.insertIdx first.val.2 (n + 1) =
        second.val.1.insertIdx second.val.2 (n + 1) := congrArg Subtype.val heq
    have hfirstlen : (first.val.1.insertIdx first.val.2 (n + 1)).length =
        first.val.1.length + 1 :=
      List.length_insertIdx_of_le_length first.property.2.1 _
    have hsecondlen : (second.val.1.insertIdx second.val.2 (n + 1)).length =
        second.val.1.length + 1 :=
      List.length_insertIdx_of_le_length second.property.2.1 _
    have hfirstbound : first.val.2 <
        (first.val.1.insertIdx first.val.2 (n + 1)).length := by omega
    have hsecondbound : second.val.2 <
        (first.val.1.insertIdx first.val.2 (n + 1)).length := by rw [hchild]; omega
    have hfirstat : (first.val.1.insertIdx first.val.2 (n + 1)).getD first.val.2 0 =
        n + 1 := by
      rw [List.getD_eq_getElem _ 0 hfirstbound]
      exact List.getElem_insertIdx_self _
    have hsecondat : (first.val.1.insertIdx first.val.2 (n + 1)).getD second.val.2 0 =
        n + 1 := by
      rw [hchild, List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_insertIdx_self _
    have hnodup : (first.val.1.insertIdx first.val.2 (n + 1)).Nodup :=
      first.property.2.2.1.nodup_iff.mpr (List.nodup_range' 1)
    have hsites : first.val.2 = second.val.2 :=
      (List.getD_inj hfirstbound hsecondbound hnodup).mp (hfirstat.trans hsecondat.symm)
    have hparents : first.val.1 = second.val.1 := by
      rw [hsites] at hchild
      exact List.insertIdx_injective _ _ hchild
    apply Subtype.ext
    exact Prod.ext hparents hsites
  · intro child
    have hlen : child.val.length = n + 1 := by
      simpa only [List.length_range'] using child.property.1.length_eq
    have hmaxmem : n + 1 ∈ child.val := by
      apply child.property.1.mem_iff.mpr
      simp only [List.mem_range', Nat.one_mul]
      exact ⟨n, by omega, by omega⟩
    obtain ⟨site, hsitechild, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
    let parent := child.val.eraseIdx site
    have hinverse : parent.insertIdx site (n + 1) = child.val := by
      simpa only [parent, hvalue] using List.insertIdx_eraseIdx_getElem hsitechild
    have hparentlen : parent.length = n := by
      simp only [parent, List.length_eraseIdx_of_lt hsitechild, hlen]
      omega
    have hsite : site ≤ parent.length := by omega
    have hparentperm : parent.Perm (List.range' 1 n) := by
      have hcons : ((n + 1) :: parent).Perm child.val := by
        simpa only [parent, hvalue] using List.getElem_cons_eraseIdx_perm hsitechild
      have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
      exact (hcons.trans (child.property.1.trans hrange)).cons_inv
    have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
      intro value hvalue
      have hm := hparentperm.mem_iff.mp hvalue
      simp only [List.mem_range', Nat.one_mul] at hm
      obtain ⟨offset, hoffset, heq⟩ := hm
      omega
    have hparentmember : parent ∈ avoiders n patterns := by
      refine ⟨hparentperm, ?_, ?_⟩
      · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
          (by rw [hinverse]; exact child.property.2.1) |>.1
      · intro pattern hpattern hocc
        obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
        apply child.property.2.2 pattern hpattern
        refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist child.val site),
          by simp⟩
        intro rank hlow hhigh
        exact (List.eraseIdx_sublist child.val site).subset (hmem rank hlow hhigh)
    refine ⟨⟨(parent, site), hparentmember, hsite, ?_⟩, ?_⟩
    · rw [hinverse]
      exact child.property
    · exact Subtype.ext hinverse

end D5.S3.Combinatorics.Fishburn.FishburnBasicParents
