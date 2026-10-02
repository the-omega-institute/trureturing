/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeq152Rotation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeq152Rotation
   mirror-E: none(waiver:minimum-rotation-block-split)
   anchors: [mathlib/module/Mathlib.Data.List.Rotate]
   utility: none
   digest: Splitting a distinct word at its minimum forces an increasing first rotation block. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq152Prefix
import Mathlib.Data.List.Rotate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeq152Rotation

open D5.S3.Combinatorics Nonnesting

theorem minimum_rotation_split (before after : List ℕ) (minimum : ℕ)
    (hnodup : (before ++ minimum :: after).Nodup)
    (hminimum : ∀ value ∈ before ++ minimum :: after, minimum ≤ value) :
    (¬ NonnestingDefs.Occurs [3, 1, 2] (before ++ minimum :: after) ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] (before ++ minimum :: after)) ↔
    before.Pairwise (· < ·) ∧
    (∀ first ∈ before, ∀ second ∈ after, first < second) ∧
    (¬ NonnestingDefs.Occurs [3, 1, 2] after ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] after) := by
  have hcharacter : ∀ (word : List ℕ) (_ : word.Nodup),
      (¬ NonnestingDefs.Occurs [3, 1, 2] word ∧
        ¬ NonnestingDefs.Occurs [3, 2, 1] word) ↔
      ∀ first second third, [first, second, third].Sublist word →
        second < first → third < first → False := by
    intro word hn
    constructor
    · rintro ⟨h201, h210⟩ first second third hsub hsecond hthird
      have hne : second ≠ third := by
        have := hsub.nodup hn
        simpa using (List.nodup_cons.mp this.tail).1
      by_cases hlt : second < third
      · apply h201
        change ArrowWilfDefs.Contains [3, 1, 2] [] 3 word
        let values := fun rank : ℕ => if rank = 1 then second else if rank = 2 then third
          else first
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hrank hmax
          have hc : rank = 1 ∨ rank = 2 := by omega
          rcases hc with rfl | rfl <;> simpa [values] using (by omega : _)
        · intro rank hrank hmax
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> simp only [values] <;>
            norm_num <;>
            apply hsub.subset <;> simp
        · simpa [values] using hsub
      · apply h210
        change ArrowWilfDefs.Contains [3, 2, 1] [] 3 word
        let values := fun rank : ℕ => if rank = 1 then third else if rank = 2 then second
          else first
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hrank hmax
          have hc : rank = 1 ∨ rank = 2 := by omega
          rcases hc with rfl | rfl <;> simpa [values] using (by omega : _)
        · intro rank hrank hmax
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> simp only [values] <;>
            norm_num <;>
            apply hsub.subset <;> simp
        · simpa [values] using hsub
    · intro hbad
      constructor
      · rintro ⟨values, hmono, _, hsub, _⟩
        have h12 : values 1 < values 2 := hmono 1 (by omega) (by decide)
        have h23 : values 2 < values 3 := hmono 2 (by omega) (by decide)
        apply hbad (values 3) (values 1) (values 2)
        · simpa using hsub
        · omega
        · omega
      · rintro ⟨values, hmono, _, hsub, _⟩
        have h12 : values 1 < values 2 := hmono 1 (by omega) (by decide)
        have h23 : values 2 < values 3 := hmono 2 (by omega) (by decide)
        apply hbad (values 3) (values 2) (values 1)
        · simpa using hsub
        · omega
        · omega
  have hafter : after.Sublist (before ++ minimum :: after) :=
    (List.sublist_cons_self minimum after).trans (List.sublist_append_right _ _)
  have hn_after := hafter.nodup hnodup
  rw [hcharacter _ hnodup, hcharacter _ hn_after]
  constructor
  · intro hbad
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_iff_forall_sublist.mpr
      intro first second hpair
      have hsub : [first, second, minimum].Sublist (before ++ minimum :: after) :=
        hpair.append (List.singleton_sublist.mpr (by simp))
      have hn := hsub.nodup hnodup
      have hmin := hminimum first (hsub.subset (by simp))
      simp only [List.nodup_cons, List.mem_cons, List.nodup_nil,
        not_or, and_true] at hn
      by_contra hnot
      exact hbad first second minimum hsub (by omega) (by omega)
    · intro first hfirst second hsecond
      have hsub : [first, minimum, second].Sublist (before ++ minimum :: after) :=
        (List.singleton_sublist.mpr hfirst).append
          ((List.singleton_sublist.mpr hsecond).cons_cons minimum)
      have hn := hsub.nodup hnodup
      have hmin := hminimum first (hsub.subset (by simp))
      simp only [List.nodup_cons, List.mem_cons, List.nodup_nil,
        not_or, and_true] at hn
      by_contra hnot
      exact hbad first minimum second hsub (by omega) (by omega)
    · intro first second third hsub hsecond hthird
      exact hbad first second third (hsub.trans hafter) hsecond hthird
  · rintro ⟨hincreasing, hseparated, hbad⟩ first second third hsub hsecond hthird
    obtain ⟨left, right, heq, hleft, hright⟩ := List.sublist_append_iff.mp hsub
    cases left with
    | nil =>
      simp only [List.nil_append] at heq
      subst right
      rcases List.sublist_cons_iff.mp hright with htail | ⟨rest, heq, hrest⟩
      · exact hbad first second third htail hsecond hthird
      · have heqfirst : first = minimum := (List.cons.inj heq).1
        have hmin := hminimum second (hsub.subset (by simp))
        omega
    | cons leftHead leftTail =>
      simp only [List.cons_append, List.cons.injEq] at heq
      rcases heq with ⟨rfl, heq⟩
      cases leftTail with
      | nil =>
        simp only [List.nil_append] at heq
        subst right
        have hfirst : first ∈ before := hleft.subset (by simp)
        have hthirdafter : third ∈ after := by
          rcases List.sublist_cons_iff.mp hright with htail | ⟨rest, heq, hrest⟩
          · exact htail.subset (by simp)
          · have heqrest : [third] = rest := (List.cons.inj heq).2
            rw [← heqrest] at hrest
            exact hrest.subset (by simp)
        have := hseparated first hfirst third hthirdafter
        omega
      | cons secondHead secondTail =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, heq⟩
        have hpair : [first, second].Sublist before := by
          exact (by simp : [first, second].Sublist (first :: second :: secondTail)).trans
            hleft
        have := hincreasing.forall_sublist hpair
        omega

theorem rotation_blocks_unique (word : List ℕ) (hnodup : word.Nodup) :
    (¬ NonnestingDefs.Occurs [3, 1, 2] word ∧
      ¬ NonnestingDefs.Occurs [3, 2, 1] word) ↔
    ∃! blocks : List (List ℕ),
      (∀ block ∈ blocks, block ≠ []) ∧ blocks.flatten.Pairwise (· < ·) ∧
      word = blocks.flatMap (fun block => block.rotate 1) := by
  have hmembers (blocks : List (List ℕ)) (value : ℕ) :
      value ∈ blocks.flatMap (fun block => block.rotate 1) ↔ value ∈ blocks.flatten := by
    simp only [List.mem_flatMap, List.mem_rotate, List.mem_flatten]
  induction word using (measure List.length).wf.induction with
  | h word ih =>
    cases word with
    | nil =>
      constructor
      · intro havoid
        refine ⟨[], by simp, ?_⟩
        intro blocks hblocks
        cases blocks with
        | nil => rfl
        | cons block rest =>
          have hn := hblocks.1 block (by simp)
          have hflat : block.rotate 1 ++ rest.flatMap (fun block => block.rotate 1) = [] :=
            hblocks.2.2.symm
          have heq : block.rotate 1 = [] :=
            (List.append_eq_nil_iff.mp hflat).1
          have hlength := congrArg List.length heq
          simp only [List.length_rotate, List.length_nil] at hlength
          exact False.elim (hn (List.eq_nil_of_length_eq_zero hlength))
      · intro hblocks
        constructor <;> rintro ⟨values, _, _, hsub, _⟩ <;>
          have hlength := hsub.length_le <;> simp at hlength
    | cons value rest =>
      have hexists : ∃ entry : ℕ, entry ∈ value :: rest := ⟨value, by simp⟩
      let minimum := Nat.find hexists
      have hminmem : minimum ∈ value :: rest := Nat.find_spec hexists
      have hminimum : ∀ entry ∈ value :: rest, minimum ≤ entry :=
        fun entry hentry => Nat.find_min' hexists hentry
      obtain ⟨before, after, hword⟩ := List.mem_iff_append.mp hminmem
      have hafterlen : after.length < (value :: rest).length := by
        rw [hword]
        simp only [List.length_append, List.length_cons]
        omega
      have hn : (before ++ minimum :: after).Nodup := hword ▸ hnodup
      have hmin : ∀ entry ∈ before ++ minimum :: after, minimum ≤ entry :=
        hword ▸ hminimum
      have hnparts := List.nodup_append.mp hn
      have hnotbefore : minimum ∉ before := by
        intro hmem
        exact hnparts.2.2 minimum hmem minimum (by simp) rfl
      have hnotafter : minimum ∉ after := (List.nodup_cons.mp hnparts.2.1).1
      have hn_after : after.Nodup := (List.nodup_cons.mp hnparts.2.1).2
      have ih_after := ih after hafterlen hn_after
      have hparse : ∀ blocks : List (List ℕ),
          (∀ block ∈ blocks, block ≠ []) → blocks.flatten.Pairwise (· < ·) →
          before ++ minimum :: after = blocks.flatMap (fun block => block.rotate 1) →
          ∃ tailBlocks, blocks = (minimum :: before) :: tailBlocks ∧
            (∀ block ∈ tailBlocks, block ≠ []) ∧
            tailBlocks.flatten.Pairwise (· < ·) ∧
            after = tailBlocks.flatMap (fun block => block.rotate 1) ∧
            before.Pairwise (· < ·) ∧
            (∀ first ∈ before, ∀ second ∈ after, first < second) := by
        intro blocks hnonempty hsorted heq
        cases blocks with
        | nil => simp at heq
        | cons block tailBlocks =>
          have hb := hnonempty block (by simp)
          cases block with
          | nil => exact False.elim (hb rfl)
          | cons head tail =>
            have hsorted' : (head :: (tail ++ tailBlocks.flatten)).Pairwise (· < ·) :=
              by simpa using hsorted
            have hhead : ∀ entry ∈ tail ++ tailBlocks.flatten, head < entry :=
              (List.pairwise_cons.mp hsorted').1
            have hheadmem : head ∈ before ++ minimum :: after := by
              rw [heq, hmembers]
              simp
            have hminin : minimum ∈ head :: (tail ++ tailBlocks.flatten) := by
              have hm : minimum ∈ ((head :: tail) :: tailBlocks).flatMap
                  (fun block => block.rotate 1) := by
                rw [← heq]; simp
              simpa using (hmembers ((head :: tail) :: tailBlocks) minimum).mp hm
            have hheadeq : head = minimum := by
              have hle := hmin head hheadmem
              rcases List.mem_cons.mp hminin with heq | hmem
              · exact heq.symm
              · have := hhead minimum hmem
                omega
            subst head
            have heq' : before ++ minimum :: after =
                tail ++ minimum :: tailBlocks.flatMap (fun block => block.rotate 1) := by
              simpa [List.rotate_cons_succ, List.append_assoc] using heq
            obtain ⟨htail, _, hafter⟩ :=
              (List.append_cons_inj_of_notMem hnotbefore hnotafter).mp heq'
            subst tail
            have hparts := List.pairwise_append.mp (List.pairwise_cons.mp hsorted').2
            refine ⟨tailBlocks, rfl, ?_, hparts.2.1, hafter, hparts.1, ?_⟩
            · intro block hblock
              exact hnonempty block (by simp [hblock])
            · intro first hfirst second hsecond
              have hmem : second ∈ tailBlocks.flatten := by
                rw [hafter, hmembers] at hsecond
                exact hsecond
              exact hparts.2.2 first hfirst second hmem
      rw [hword]
      constructor
      · intro havoid
        obtain ⟨hincreasing, hseparated, hafteravoid⟩ :=
          (minimum_rotation_split before after minimum hn hmin).mp havoid
        obtain ⟨tailBlocks, htail, hunique⟩ := ih_after.mp hafteravoid
        refine ⟨(minimum :: before) :: tailBlocks, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro block hblock
            rcases List.mem_cons.mp hblock with rfl | hblock
            · simp
            · exact htail.1 block hblock
          · change (minimum :: (before ++ tailBlocks.flatten)).Pairwise (· < ·)
            apply List.pairwise_cons.mpr
            refine ⟨?_, List.pairwise_append.mpr ⟨hincreasing, htail.2.1, ?_⟩⟩
            · intro entry hentry
              rcases List.mem_append.mp hentry with hpre | hpost
              · have hle := hmin entry (by simp [hpre])
                have hne : entry ≠ minimum := by intro heq; subst entry; contradiction
                omega
              · have hmem : entry ∈ after := by rw [htail.2.2, hmembers]; exact hpost
                have hle := hmin entry (by simp [hmem])
                have hne : entry ≠ minimum := by intro heq; subst entry; contradiction
                omega
            · intro first hfirst second hsecond
              apply hseparated first hfirst second
              rw [htail.2.2, hmembers]
              exact hsecond
          · simp [List.rotate_cons_succ, List.append_assoc, ← htail.2.2]
        · intro blocks hblocks
          obtain ⟨otherTail, rfl, hnonempty, hsorted, heq, _, _⟩ :=
            hparse blocks hblocks.1 hblocks.2.1 hblocks.2.2
          have heqtail := hunique otherTail ⟨hnonempty, hsorted, heq⟩
          rw [heqtail]
      · rintro ⟨blocks, hblocks, hunique⟩
        obtain ⟨tailBlocks, rfl, hnonempty, hsorted, heq, hincreasing, hseparated⟩ :=
          hparse blocks hblocks.1 hblocks.2.1 hblocks.2.2
        have haftercert : ∃! candidate : List (List ℕ),
            (∀ block ∈ candidate, block ≠ []) ∧ candidate.flatten.Pairwise (· < ·) ∧
            after = candidate.flatMap (fun block => block.rotate 1) := by
          refine ⟨tailBlocks, ⟨hnonempty, hsorted, heq⟩, ?_⟩
          intro other hother
          have hotherfull :
              (∀ block ∈ (minimum :: before) :: other, block ≠ []) ∧
              ((minimum :: before) :: other).flatten.Pairwise (· < ·) ∧
              before ++ minimum :: after =
                ((minimum :: before) :: other).flatMap (fun block => block.rotate 1) := by
            refine ⟨?_, ?_, ?_⟩
            · intro block hblock
              rcases List.mem_cons.mp hblock with rfl | hblock
              · simp
              · exact hother.1 block hblock
            · change (minimum :: (before ++ other.flatten)).Pairwise (· < ·)
              apply List.pairwise_cons.mpr
              refine ⟨?_, List.pairwise_append.mpr ⟨hincreasing, hother.2.1, ?_⟩⟩
              · intro entry hentry
                rcases List.mem_append.mp hentry with hpre | hpost
                · have hle := hmin entry (by simp [hpre])
                  have hne : entry ≠ minimum := by intro heq; subst entry; contradiction
                  omega
                · have hmem : entry ∈ after := by rw [hother.2.2, hmembers]; exact hpost
                  have hle := hmin entry (by simp [hmem])
                  have hne : entry ≠ minimum := by intro heq; subst entry; contradiction
                  omega
              · intro first hfirst second hsecond
                apply hseparated first hfirst second
                rw [hother.2.2, hmembers]
                exact hsecond
            · simp [List.rotate_cons_succ, List.append_assoc, ← hother.2.2]
          exact (List.cons.inj (hunique ((minimum :: before) :: other) hotherfull)).2
        exact (minimum_rotation_split before after minimum hn hmin).mpr
          ⟨hincreasing, hseparated, ih_after.mpr haftercert⟩

end D5.S3.Combinatorics.InversionSeq.InversionSeq152Rotation
