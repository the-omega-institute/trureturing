/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveAInvariant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveAInvariant
   mirror-E: none(waiver:a-active-site-size-induction)
   anchors: []
   utility: none
   digest: Maximum deletion and reinsertion establish the A invariant for every nonempty avoider. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveASites
import D5.S3.Combinatorics.Fishburn.FishburnTenFivePrepend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveAInvariant

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion FishburnBasicPatterns
open FishburnTenFiveASites FishburnTenFivePrepend

set_option maxHeartbeats 1600000 in
theorem all_A_site_invariant : ∀ n : ℕ, 1 ≤ n → ∀ p : List ℕ,
    p ∈ avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]] →
    ∃ start : ℕ, 1 ≤ start ∧ start ≤ p.length ∧ ∃ three : Prop,
      (∀ gap, gap ≤ p.length →
        (p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
          gap = 0 ∨ gap = start ∨ three ∧ gap = start + 1)) ∧
      (three → start < p.length ∧ p.getD (start - 1) 0 < p.getD start 0 ∧
        ∃ position ≤ start, p.getD position 0 = n) := by
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
          [1].insertIdx gap 2 ∈ avoiders 2 [[1, 3, 2, 4], [1, 4, 2, 3]] := by
        intro gap hgap
        have hc : gap = 0 ∨ gap = 1 := by omega
        rcases hc with rfl | rfl <;> refine ⟨by decide, ?_, ?_⟩
        all_goals first
          | (intro before later hfar hbound; change later < 2 at hbound; omega)
          | (intro pattern hpattern hocc
             have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
               simpa using hpattern
             rcases hc with rfl | rfl <;>
               obtain ⟨values, _, _, hsub, _⟩ := hocc <;>
               have hlen := hsub.length_le <;>
               simp only [List.length_map, List.length_cons, List.length_nil,
                 List.insertIdx_zero, List.insertIdx_succ_cons] at hlen <;>
               omega)
      refine ⟨1, by omega, by simp, False, ?_, by intro hfalse; exact hfalse.elim⟩
      intro gap hgap
      change gap ≤ 1 at hgap
      constructor
      · intro _
        have hc : gap = 0 ∨ gap = 1 := by omega
        exact hc.elim Or.inl (Or.inr ∘ Or.inl)
      · intro _
        exact hroot gap hgap
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
      have hparentmember : parent ∈ avoiders n [[1, 3, 2, 4], [1, 4, 2, 3]] := by
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
          avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
        rwa [hinverse]
      obtain ⟨start, hstart, hstartbound, three, hshape, hascent⟩ :=
        ih hpositive parent hparentmember
      by_cases hsitezero : site = 0
      · have hprepend : p = (n + 1) :: parent := by
          rw [hsitezero, List.insertIdx_zero] at hinverse
          exact hinverse.symm
        refine ⟨start + 1, by omega, by omega, three, ?_, ?_⟩
        · intro gap hgap
          by_cases hgapzero : gap = 0
          · subst gap
            have ht := maximum_pattern_tests (n + 1) p hmember.1 0 (by omega)
            have hmax : ∀ value ∈ p, value < n + 2 := by
              intro value hvalue
              have hm := hmember.1.mem_iff.mp hvalue
              simp only [List.mem_range', Nat.one_mul] at hm
              obtain ⟨offset, hoffset, heq⟩ := hm
              omega
            have hz : p.insertIdx 0 (n + 2) ∈
                avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
              refine ⟨?_, ?_, ?_⟩
              · apply (List.perm_insertIdx (n + 2) p (by omega)).trans
                apply (hmember.1.cons (n + 2)).trans
                have hrange : List.range' 1 (n + 2) =
                    List.range' 1 (n + 1) ++ [n + 2] := by
                  simpa only [Nat.one_mul, Nat.add_assoc, Nat.reduceAdd,
                    show 1 + (n + 1) = n + 2 by omega] using
                    (List.range'_concat (s := 1) (n := n + 1) (step := 1))
                rw [hrange]
                simpa using (List.perm_append_comm (l₁ := [n + 2])
                  (l₂ := List.range' 1 (n + 1)))
              · apply (isFishburn_insertIdx_max_iff p (n + 2) 0 (by omega) hmax).mpr
                exact ⟨hmember.2.1, by intro before later hcross; omega⟩
              · intro pattern hpattern hocc
                have hc : pattern = [1, 3, 2, 4] ∨ pattern = [1, 4, 2, 3] := by
                  simpa using hpattern
                rcases hc with rfl | rfl
                · rcases ht.1.mp hocc with hprevious | ⟨_, _, third, _, _, hthird, _, _⟩
                  · exact hmember.2.2 _ (by simp) hprevious
                  · omega
                · rcases ht.2.2.mp hocc with hprevious | ⟨first, _, _, hfirst, _, _, _, _, _⟩
                  · exact hmember.2.2 _ (by simp) hprevious
                  · omega
            exact ⟨fun _ => Or.inl rfl, fun _ => hz⟩
          · have hgapold : gap - 1 ≤ parent.length := by omega
            have hsucc : gap - 1 + 1 = gap := by omega
            have hrule := (prepend_site_rules n parent hpositive hparentperm
              hparentmember.2.1 (gap - 1) hgapold).1
            have hiff : p.insertIdx gap (n + 2) ∈
                avoiders (n + 2) [[1, 3, 2, 4], [1, 4, 2, 3]] ↔
                gap - 1 ≠ 0 ∧ parent.insertIdx (gap - 1) (n + 1) ∈
                  avoiders (n + 1) [[1, 3, 2, 4], [1, 4, 2, 3]] := by
              simpa only [← hprepend, hsucc] using hrule
            rw [hiff, hshape (gap - 1) hgapold]
            constructor
            · rintro ⟨hne, hz | hs | ⟨hthree, hs⟩⟩
              · contradiction
              · exact Or.inr (Or.inl (by omega))
              · exact Or.inr (Or.inr ⟨hthree, by omega⟩)
            · rintro (hz | hs | ⟨hthree, hs⟩)
              · contradiction
              · exact ⟨by omega, Or.inr (Or.inl (by omega))⟩
              · exact ⟨by omega, Or.inr (Or.inr ⟨hthree, by omega⟩)⟩
        · intro hthree
          have ha := hascent hthree
          refine ⟨by omega, ?_, 0, by omega, ?_⟩
          · have hb : ((n + 1) :: parent).getD start 0 = parent.getD (start - 1) 0 := by
              have hs : start - 1 + 1 = start := by omega
              rw [← hs]
              simp only [List.getD_cons_succ, Nat.add_sub_cancel]
            rw [hprepend, Nat.add_sub_cancel, hb, List.getD_cons_succ]
            exact ha.2.1
          · rw [hprepend]
            rfl
      · have hsitepositive : 0 < site := by omega
        let newthree : Prop := ∃ earlier < site, parent.getD earlier 0 = n
        refine ⟨site, by omega, by omega, newthree, ?_, ?_⟩
        · have hupdate := positive_A_site_update n parent hparentmember start hstart three
            hshape (fun hthree => ⟨(hascent hthree).1, (hascent hthree).2.1⟩)
            site hsitepositive hsite hactive
          intro gap hgap
          have hu := hupdate gap (by rwa [hinverse])
          simpa only [hinverse, newthree, or_assoc, and_comm] using hu
        · intro _
          have hbefore : p.getD (site - 1) 0 = parent.getD (site - 1) 0 := by
            rw [← hinverse, List.getD_eq_getElem _ 0 (by omega),
              List.getElem_insertIdx_of_lt (by omega),
              List.getD_eq_getElem parent 0 (by omega)]
          have hat : p.getD site 0 = n + 1 := by
            rw [← hinverse, List.getD_eq_getElem _ 0 (by omega)]
            exact List.getElem_insertIdx_self _
          refine ⟨by omega, ?_, site, by omega, hat⟩
          rw [hbefore, hat, List.getD_eq_getElem parent 0 (by omega)]
          exact hmaxparent _ (List.getElem_mem _)

end D5.S3.Combinatorics.Fishburn.FishburnTenFiveAInvariant
