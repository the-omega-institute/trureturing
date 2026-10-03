/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveBInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveBInvariant
   mirror-E: none(waiver:b-active-site-size-induction)
   anchors: []
   utility: none
   digest: Maximum deletion establishes the B interval and its monotone prefix invariant. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveBSites
import D5.S3.Combinatorics.Fishburn.FishburnTenFivePrepend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveBInvariant

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns
open FishburnTenFiveBSites FishburnTenFivePrepend

set_option maxHeartbeats 2400000 in
theorem all_B_site_invariant : ∀ n : ℕ, 1 ≤ n → ∀ p : List ℕ,
    p ∈ avoiders n [[1, 3, 2, 4], [3, 1, 2, 4]] →
    ∃ start finish : ℕ, 1 ≤ start ∧ start ≤ finish ∧ finish ≤ p.length ∧
      (∀ gap, gap ≤ p.length →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
          gap = 0 ∨ start ≤ gap ∧ gap ≤ finish)) ∧
      (∀ first second, first < second → second < start →
        p.getD second 0 < p.getD first 0) ∧
      (∀ edge, start ≤ edge → edge < finish →
        p.getD (edge - 1) 0 < p.getD edge 0) ∧
      (∀ position, position < p.length → p.getD position 0 = n →
        (position < start → start = finish) ∧
        (start ≤ position → position < finish → position + 1 = finish)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro hn p hmember
    by_cases hzero : n = 0
    · subst n
      have hperm : p.Perm [1] := hmember.1
      have heq := List.perm_singleton.mp hperm
      subst p
      have hroot : ∀ gap, gap ≤ 1 →
          [1].insertIdx gap 2 ∈ avoiders 2 [[1, 3, 2, 4], [3, 1, 2, 4]] := by
        intro gap hgap
        have hc : gap = 0 ∨ gap = 1 := by omega
        rcases hc with rfl | rfl <;> refine ⟨by decide, ?_, ?_⟩
        all_goals first
          | (intro before later hfar hbound; change later < 2 at hbound; omega)
          | (intro pattern hpattern hocc
             have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
               simpa using hpattern
             rcases hc with rfl | rfl <;>
               obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
               have hlen := hsub.length_le <;>
               simp only [List.length_map, List.length_cons, List.length_nil,
                 List.insertIdx_zero, List.insertIdx_succ_cons] at hlen <;>
               omega)
      refine ⟨1, 1, by omega, by omega, by simp, ?_, ?_, ?_, ?_⟩
      · intro gap hgap
        change gap ≤ 1 at hgap
        constructor
        · intro _
          by_cases hz : gap = 0
          · exact Or.inl hz
          · exact Or.inr ⟨by omega, by omega⟩
        · intro _
          exact hroot gap hgap
      · intro first second hfs hs
        omega
      · intro edge hlow hhigh
        omega
      · intro position hposition _
        change position < 1 at hposition
        exact ⟨fun _ => rfl, by intros; omega⟩
    · have hpositive : 1 ≤ n := by omega
      have hlen : p.length = n + 1 := by
        simpa only [List.length_range'] using hmember.1.length_eq
      have hmaxmem : n + 1 ∈ p := by
        apply hmember.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n, by omega, by omega⟩
      obtain ⟨site, hsitep, hvalue⟩ := List.mem_iff_getElem.mp hmaxmem
      let parent := p.eraseIdx site
      have hinverse : parent.insertIdx site (n + 1) = p := by
        simpa only [parent, hvalue] using List.insertIdx_eraseIdx_getElem hsitep
      have hparentlen : parent.length = n := by
        simp only [parent, List.length_eraseIdx_of_lt hsitep, hlen]
        omega
      have hsite : site ≤ parent.length := by omega
      have hchildlen : (parent.insertIdx site (n + 1)).length = parent.length + 1 :=
        List.length_insertIdx_of_le_length hsite (n + 1)
      have hparentperm : parent.Perm (List.range' 1 n) := by
        have hcons : ((n + 1) :: parent).Perm p := by
          simpa only [parent, hvalue] using List.getElem_cons_eraseIdx_perm hsitep
        have hrange : (List.range' 1 (n + 1)).Perm ((n + 1) :: List.range' 1 n) := by
          rw [List.range'_concat]
          simpa [Nat.add_comm] using
            (List.perm_append_comm (l₁ := List.range' 1 n) (l₂ := [n + 1]))
        exact (hcons.trans (hmember.1.trans hrange)).cons_inv
      have hmaxparent : ∀ value ∈ parent, value < n + 1 := by
        intro value hvalue
        have hm := hparentperm.mem_iff.mp hvalue
        simp only [List.mem_range', Nat.one_mul] at hm
        obtain ⟨offset, hoffset, heq⟩ := hm
        omega
      have hparentmember : parent ∈ avoiders n [[1, 3, 2, 4], [3, 1, 2, 4]] := by
        refine ⟨hparentperm, ?_, ?_⟩
        · apply (isFishburn_insertIdx_max_iff parent (n + 1) site hsite hmaxparent).mp
            (by rw [hinverse]; exact hmember.2.1) |>.1
        · intro pattern hpattern hocc
          obtain ⟨values, hstep, hmem, hsub, hrel⟩ := hocc
          apply hmember.2.2 pattern hpattern
          refine ⟨values, hstep, ?_, hsub.trans (List.eraseIdx_sublist p site), by simp⟩
          intro rank hlow hhigh
          exact (List.eraseIdx_sublist p site).subset (hmem rank hlow hhigh)
      have hactive : parent.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
        rwa [hinverse]
      obtain ⟨start, finish, hstart, hsf, hfinish, hshape, hdecreasing, hascent, _⟩ :=
        ih hpositive parent hparentmember
      have hmax : ∀ value ∈ p, value < n + 2 := by
        intro value hvalue
        have hm := hmember.1.mem_iff.mp hvalue
        simp only [List.mem_range', Nat.one_mul] at hm
        obtain ⟨offset, hoffset, heq⟩ := hm
        omega
      have hzeroactive : p.insertIdx 0 (n + 2) ∈
          avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] := by
        refine ⟨?_, ?_, ?_⟩
        · apply (List.perm_insertIdx (n + 2) p (by omega)).trans
          apply (hmember.1.cons (n + 2)).trans
          have hrange : List.range' 1 (n + 2) = List.range' 1 (n + 1) ++ [n + 2] := by
            simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
              show 1 + (n + 1) = n + 2 by omega] using
              (List.range'_concat (s := 1) (n := n + 1) (step := 1))
          rw [hrange]
          simpa using (List.perm_append_comm (l₁ := [n + 2])
            (l₂ := List.range' 1 (n + 1)))
        · apply (isFishburn_insertIdx_max_iff p (n + 2) 0 (by omega) hmax).mpr
          exact ⟨hmember.2.1, by intro before later hcross; omega⟩
        · intro pattern hpattern hocc
          have ht := maximum_pattern_tests (n + 1) p hmember.1 0 (by omega)
          have hc : pattern = [1, 3, 2, 4] ∨ pattern = [3, 1, 2, 4] := by
            simpa using hpattern
          rcases hc with rfl | rfl
          · rcases ht.1.mp hocc with hprevious | ⟨_, _, third, _, _, hthird, _, _⟩
            · exact hmember.2.2 _ (by simp) hprevious
            · omega
          · rcases ht.2.1.mp hocc with hprevious | ⟨_, _, third, _, _, hthird, _, _⟩
            · exact hmember.2.2 _ (by simp) hprevious
            · omega
      by_cases hsitezero : site = 0
      · have hprepend : p = (n + 1) :: parent := by
          rw [hsitezero, List.insertIdx_zero] at hinverse
          exact hinverse.symm
        have htail : ∀ index, p.getD (index + 1) 0 = parent.getD index 0 := by
          intro index
          rw [hprepend, List.getD_cons_succ]
        refine ⟨start + 1, start + 1, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · intro gap hgap
          by_cases hgapzero : gap = 0
          · subst gap
            exact ⟨fun _ => Or.inl rfl, fun _ => hzeroactive⟩
          · have hgapold : gap - 1 ≤ parent.length := by omega
            have hsucc : gap - 1 + 1 = gap := by omega
            have hrule := (prepend_site_rules n parent hpositive hparentperm
              hparentmember.2.1 (gap - 1) hgapold).2
            have hiff : p.insertIdx gap (n + 2) ∈
                avoiders (n + 2) [[1, 3, 2, 4], [3, 1, 2, 4]] ↔
                gap - 1 ≠ 0 ∧ parent.insertIdx (gap - 1) (n + 1) ∈
                  avoiders (n + 1) [[1, 3, 2, 4], [3, 1, 2, 4]] ∧
                ∀ first second, first < second → second < gap - 1 →
                  parent.getD second 0 < parent.getD first 0 := by
              simpa only [← hprepend, hsucc] using hrule
            rw [hiff]
            constructor
            · rintro ⟨hne, hparentactive, hdec⟩
              have hrange : start ≤ gap - 1 ∧ gap - 1 ≤ finish := by
                rcases (hshape (gap - 1) hgapold).mp hparentactive with hz | hr
                · contradiction
                · exact hr
              have heq : gap - 1 = start := by
                by_contra hnot
                have ha := hascent start (by omega) (by omega)
                have hd := hdec (start - 1) start (by omega) (by omega)
                omega
              exact Or.inr ⟨by omega, by omega⟩
            · rintro (hz | ⟨hlow, hhigh⟩)
              · contradiction
              · have heq : gap - 1 = start := by omega
                refine ⟨by omega, ?_, ?_⟩
                · exact (hshape (gap - 1) hgapold).mpr (Or.inr ⟨by omega, by omega⟩)
                · simpa only [heq] using hdecreasing
        · intro first second hfs hs
          by_cases hfirst : first = 0
          · subst first
            have hsecond : second - 1 + 1 = second := by omega
            rw [← hsecond, htail, hprepend, List.getD_cons_zero]
            rw [List.getD_eq_getElem parent 0 (by omega)]
            exact hmaxparent _ (List.getElem_mem _)
          · have hf : first - 1 + 1 = first := by omega
            have hsec : second - 1 + 1 = second := by omega
            rw [← hf, ← hsec, htail, htail]
            exact hdecreasing (first - 1) (second - 1) (by omega) (by omega)
        · intro edge hlow hhigh
          omega
        · intro position hposition hentry
          refine ⟨fun _ => rfl, ?_⟩
          intro hlow hhigh
          omega
      · have hsitepositive : 0 < site := by omega
        have hsrange : start ≤ site ∧ site ≤ finish := by
          rcases (hshape site hsite).mp hactive with hz | hr
          · contradiction
          · exact hr
        have hbefore : ∀ index, index < site → p.getD index 0 = parent.getD index 0 := by
          intro index hindex
          rw [← hinverse, List.getD_eq_getElem _ 0 (by omega),
            List.getElem_insertIdx_of_lt hindex,
            List.getD_eq_getElem parent 0 (by omega)]
        have hat : p.getD site 0 = n + 1 := by
          rw [List.getD_eq_getElem p 0 hsitep]
          exact hvalue
        let extra : Prop := ∃ earlier < site, parent.getD earlier 0 = n
        classical
        let last := if extra then site + 1 else site
        have hlast : site ≤ last ∧ last ≤ site + 1 := by
          dsimp [last]
          split_ifs <;> omega
        refine ⟨start, last, hstart, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · have hupdate := positive_B_site_update n parent hparentmember start finish hstart
            hfinish hshape hascent site hsitepositive hsite hactive
          intro gap hgap
          have hu := hupdate gap (by rwa [hinverse])
          rw [hinverse] at hu
          rw [hu]
          change (gap = 0 ∨ start ≤ gap ∧ gap ≤ site ∨ gap = site + 1 ∧ extra) ↔ _
          dsimp [last]
          split_ifs with hextra
          · constructor
            · rintro (hz | ⟨hlow, hhigh⟩ | ⟨heq, _⟩)
              · exact Or.inl hz
              · exact Or.inr ⟨hlow, by omega⟩
              · exact Or.inr ⟨by omega, by omega⟩
            · rintro (hz | ⟨hlow, hhigh⟩)
              · exact Or.inl hz
              · by_cases hnext : gap = site + 1
                · exact Or.inr (Or.inr ⟨hnext, hextra⟩)
                · exact Or.inr (Or.inl ⟨hlow, by omega⟩)
          · constructor
            · rintro (hz | ⟨hlow, hhigh⟩ | ⟨_, hex⟩)
              · exact Or.inl hz
              · exact Or.inr ⟨hlow, hhigh⟩
              · exact False.elim (hextra hex)
            · rintro (hz | hr)
              · exact Or.inl hz
              · exact Or.inr (Or.inl hr)
        · intro first second hfs hs
          rw [hbefore second (by omega), hbefore first (by omega)]
          exact hdecreasing first second hfs hs
        · intro edge hlow hhigh
          by_cases hedge : edge < site
          · rw [hbefore (edge - 1) (by omega), hbefore edge hedge]
            exact hascent edge hlow (by omega)
          · have heq : edge = site := by omega
            subst edge
            rw [hbefore (site - 1) (by omega), hat,
              List.getD_eq_getElem parent 0 (by omega)]
            exact hmaxparent _ (List.getElem_mem _)
        · intro position hposition hentry
          have heq : position = site := by
            apply (List.getD_inj hposition hsitep
              (hmember.1.nodup_iff.mpr (List.nodup_range' 1))).mp
            exact hentry.trans hat.symm
          constructor
          · intro hlow
            omega
          · intro hlow hhigh
            omega

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveBInvariant
