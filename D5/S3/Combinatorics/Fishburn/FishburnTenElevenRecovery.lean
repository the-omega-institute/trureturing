/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenElevenRecovery
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenElevenRecovery
   mirror-E: none(waiver:exceptional-fishburn-parent-induction)
   anchors: [mathlib/module/Mathlib.Data.List.Sort]
   utility: none
   digest: Maximum deletion recovers a bounded pair from every exceptional Fishburn parent. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenElevenFamily
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenElevenRecovery

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnTenElevenSites
open FishburnBasicThreePatterns FishburnBasicInsertion FishburnTenElevenFamily

theorem pair_recovery (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[1, 2, 4, 3], [2, 1, 3, 4]]) (hn : 1 ≤ n)
    (havoid : ¬ NonnestingDefs.Occurs [2, 1, 3] p) (hlast : p.getD (n - 1) 0 ≠ 1) :
    ∃ a b, 2 ≤ b ∧ b ≤ a ∧ a ≤ n ∧ p = pairPermutation n a b := by
  have hmaximum (n : ℕ) (patterns : List (List ℕ)) :
      Function.Surjective (fun entry : {entry : List ℕ × ℕ //
        entry.1 ∈ avoiders n patterns ∧ entry.2 ≤ entry.1.length ∧
          entry.1.insertIdx entry.2 (n + 1) ∈ avoiders (n + 1) patterns} =>
        (⟨entry.val.1.insertIdx entry.val.2 (n + 1), entry.property.2.2⟩ :
          avoiders (n + 1) patterns)) := by
    intro child
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
        simpa only [Nat.add_comm, Nat.one_mul, List.singleton_append] using
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
  have hleft (size lower upper : ℕ) (hupper : upper ≤ size) :
      pairPermutation (size + 1) upper lower =
        (size + 1) :: pairPermutation size upper lower := by
    have hseq : List.range' (upper + 1) (size + 1 - upper) =
        List.range' (upper + 1) (size - upper) ++ [size + 1] := by
      have hc : size + 1 - upper = size - upper + 1 := by omega
      rw [hc, List.range'_concat]
      congr 1
      congr 1
      omega
    simp only [pairPermutation, hseq, List.reverse_append, List.reverse_singleton,
      List.cons_append, List.nil_append]
  have hmiddle (size lower : ℕ) (hlower : lower ≤ size) :
      pairPermutation (size + 1) (size + 1) lower =
        (pairPermutation size size lower).insertIdx 1 (size + 1) := by
    have hseq : List.range' (lower + 1) (size + 1 - lower) =
        List.range' (lower + 1) (size - lower) ++ [size + 1] := by
      have hc : size + 1 - lower = size - lower + 1 := by omega
      rw [hc, List.range'_concat]
      congr 1
      congr 1
      omega
    simp only [pairPermutation, Nat.sub_self, List.range'_zero, List.reverse_nil,
      List.nil_append, hseq, List.reverse_append,
      List.reverse_singleton, List.cons_append, List.insertIdx_succ_cons,
      List.insertIdx_zero]
  have hidentity (size : ℕ) (hs : 1 ≤ size) :
      pairPermutation size size size = List.range' 1 size := by
    cases size with
    | zero => omega
    | succ size => simp [pairPermutation, List.range'_succ]
  induction n generalizing p with
  | zero => omega
  | succ size ih =>
    by_cases hz : size = 0
    · subst size
      have hp : p = [1] := List.perm_singleton.mp (by simpa using hparent.1)
      simp [hp] at hlast
    have hsize : 1 ≤ size := by omega
    obtain ⟨entry, heq⟩ := (hmaximum size
      [[1, 2, 4, 3], [2, 1, 3, 4]]) ⟨p, hparent⟩
    obtain ⟨⟨parent, site⟩, hentry⟩ := entry
    have hp : parent.insertIdx site (size + 1) = p := congrArg Subtype.val heq
    subst p
    have hclass := hentry.1
    have hsite := hentry.2.1
    have hactive := hentry.2.2
    change parent ∈ avoiders size [[1, 2, 4, 3], [2, 1, 3, 4]] at hclass
    change site ≤ parent.length at hsite
    change parent.insertIdx site (size + 1) ∈
      avoiders (size + 1) [[1, 2, 4, 3], [2, 1, 3, 4]] at hactive
    have hlen : parent.length = size := by simpa using hclass.1.length_eq
    have hnodup : parent.Nodup := hclass.1.nodup_iff.mpr (List.nodup_range' 1)
    have htest := maximum_213_test size parent hclass.1 site hsite
    have hno : ¬ NonnestingDefs.Occurs [2, 1, 3] parent := by
      intro ho
      exact havoid (htest.mpr (Or.inl ho))
    have hpref (first second : ℕ) (hfs : first < second) (hs : second < site) :
        ¬ parent.getD second 0 < parent.getD first 0 := by
      intro hlt
      exact havoid (htest.mpr (Or.inr ⟨first, second, hfs, hs, hlt⟩))
    have hlasttransport (hcut : site < size) :
        (parent.insertIdx site (size + 1)).getD size 0 = parent.getD (size - 1) 0 := by
      have hbound : size < (parent.insertIdx site (size + 1)).length := by
        rw [List.length_insertIdx_of_le_length hsite]
        omega
      rw [List.getD_eq_getElem _ 0 hbound, List.getElem_insertIdx_of_gt (by omega),
        List.getD_eq_getElem parent 0 (by omega)]
    rcases (fishburn_active_sites size parent hclass site hsite).mp hactive with
      hzero | ⟨one, hob, ho, hsiteone⟩ | ⟨hend, _⟩
    · have hparentlast : parent.getD (size - 1) 0 ≠ 1 := by
        rw [show size + 1 - 1 = size by omega, hlasttransport (by omega)] at hlast
        exact hlast
      obtain ⟨a, b, hb, hba, ha, hp⟩ := ih parent hclass hsize hno hparentlast
      refine ⟨a, b, hb, hba, by omega, ?_⟩
      rw [hzero, List.insertIdx_zero, hp, hleft size b a ha]
    · have hone : one = 0 := by
        by_contra hnot
        have hmem : parent.getD 0 0 ∈ parent := by
          rw [List.getD_eq_getElem parent 0 (by omega)]
          exact List.getElem_mem (by omega)
        have hr := hclass.1.mem_iff.mp hmem
        simp only [List.mem_range', Nat.one_mul] at hr
        obtain ⟨offset, hh, hv⟩ := hr
        have hne : parent.getD 0 0 ≠ 1 := by
          intro he
          have := (List.getD_inj (by omega) hob hnodup).mp (he.trans ho.symm)
          omega
        exact hpref 0 one (by omega) (by omega) (by omega)
      subst one
      have hsiteone : site = 1 := by omega
      subst site
      by_cases hs : size = 1
      · rcases hs with rfl
        have hp : parent = [1] := List.perm_singleton.mp (by simpa using hclass.1)
        refine ⟨2, 2, le_rfl, le_rfl, le_rfl, ?_⟩
        simp [hp, pairPermutation, List.insertIdx_succ_cons, List.insertIdx_zero]
      · have hparentlast : parent.getD (size - 1) 0 ≠ 1 := by
          rw [show size + 1 - 1 = size by omega, hlasttransport (by omega)] at hlast
          exact hlast
        obtain ⟨a, b, hb, hba, ha, hp⟩ := ih parent hclass hsize hno hparentlast
        have hae : a = size := by
          by_contra hnot
          have hlead : 0 < (List.range' (a + 1) (size - a)).reverse.length := by
            simp only [List.length_reverse, List.length_range']
            omega
          let lead := (List.range' (a + 1) (size - a)).reverse
          let rest := [1] ++ (List.range' (b + 1) (a - b)).reverse ++ List.range' 2 (b - 1)
          have hleadbound : 0 < lead.length := hlead
          have hdef : pairPermutation size a b = lead ++ rest := by
            simp only [pairPermutation, lead, rest, List.append_assoc]
          have hfirst : (pairPermutation size a b).getD 0 0 = size := by
            rw [hdef, List.getD_eq_getElem _ 0 (by
              simp only [List.length_append]; omega),
              List.getElem_append_left (by exact hlead),
              List.getElem_reverse (by exact hlead), List.getElem_range']
            simp only [List.length_range', Nat.sub_zero, Nat.one_mul]
            omega
          rw [hp, hfirst] at ho
          omega
        subst a
        refine ⟨size + 1, b, hb, by omega, le_rfl, ?_⟩
        rw [hp, hmiddle size b hba]
    · have hincreasing : parent.Pairwise (· < ·) := by
        rw [List.pairwise_iff_getElem]
        intro first second hf hs hfs
        have hne : parent.getD first 0 ≠ parent.getD second 0 := by
          intro he
          have := (List.getD_inj hf hs hnodup).mp he
          omega
        have hnolt := hpref first second hfs (by omega)
        have hlt : parent.getD first 0 < parent.getD second 0 := by omega
        simpa only [List.getD_eq_getElem parent 0 hf, List.getD_eq_getElem parent 0 hs]
          using hlt
      have hp : parent = List.range' 1 size :=
        hincreasing.eq_of_mem_iff List.pairwise_lt_range' (fun _ => hclass.1.mem_iff)
      refine ⟨size + 1, size + 1, by omega, le_rfl, le_rfl, ?_⟩
      rw [hend, List.insertIdx_length_self, hp, hidentity (size + 1) (by omega),
        List.range'_concat]
      simp [Nat.add_comm]

end D5.S3.Combinatorics.Fishburn.FishburnTenElevenRecovery
