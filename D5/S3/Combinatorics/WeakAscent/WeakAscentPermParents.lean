/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentPermParents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentPermParents
   mirror-E: none(waiver:permutation-restriction)
   anchors: [mathlib/module/Mathlib.Data.List.Permutation]
   utility: none
   digest: Unique maximum deletion and repeated restriction preserve the avoiding class. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentPermChildren
import Mathlib.Data.List.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentPermParents

open WeakAscentDefs WeakAscentInsertion

theorem restriction_avoids (n : ℕ) (q : List ℕ) (hq : q ∈ permAvoiders n)
    (m : ℕ) (hm : m ≤ n) : q.filter (fun value => value ≤ m) ∈ permAvoiders m := by
  have maximum_parent (n : ℕ) (q : List ℕ) (hq : q ∈ permAvoiders (n + 1)) :
      ∃ site, site ≤ n ∧ (q.filter (fun value => value ≤ n)) ∈ permAvoiders n ∧
        q = (q.filter (fun value => value ≤ n)).insertIdx site (n + 1) := by
    have hperm := hq.1
    have hlength : q.length = n + 1 := by simpa using hperm.length_eq
    have hnodup : q.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
    have bound (value : ℕ) (hvalue : value ∈ q) : value ≤ n + 1 := by
      obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
      omega
    have hmaxmem : n + 1 ∈ q :=
      hperm.mem_iff.mpr (List.mem_range'.mpr ⟨n, by omega, by omega⟩)
    let site := q.idxOf (n + 1)
    have hsite : site < q.length := List.idxOf_lt_length_iff.mpr hmaxmem
    have hsitevalue : q[site] = n + 1 := List.getElem_idxOf hsite
    have hsite_option : q.idxOf? (n + 1) = some site := by
      apply List.idxOf?_eq_some_iff.mpr
      refine ⟨hsite, hsitevalue, ?_⟩
      intro earlier hearlier heq
      have hread : q.getD earlier 0 = q.getD site 0 := by
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hsite]
        exact heq.trans hsitevalue.symm
      have hsame := (List.getD_inj (show earlier < q.length by omega) hsite hnodup).mp hread
      omega
    have erase_index : q.erase (n + 1) = q.eraseIdx site := by
      rw [List.erase_eq_eraseIdx, hsite_option]
    have erase_filter : q.erase (n + 1) = q.filter (fun value => value ≤ n) := by
      rw [hnodup.erase_eq_filter]
      apply List.filter_congr
      intro value hvalue
      have hbound := bound value hvalue
      by_cases hle : value ≤ n
      · have hne : value ≠ n + 1 := by omega
        simp [hle, hne]
      · have heq : value = n + 1 := by omega
        simp [heq]
    have reconstruct : (q.filter (fun value => value ≤ n)).insertIdx site (n + 1) = q := by
      rw [← erase_filter, erase_index, ← hsitevalue]
      exact List.insertIdx_eraseIdx_getElem hsite
    have hparentperm : (q.filter (fun value => value ≤ n)).Perm (List.range' 1 n) := by
      rw [← erase_filter]
      have hnot : n + 1 ∉ List.range' 1 n := by
        intro hmem
        obtain ⟨index, hindex, heq⟩ := List.mem_range'.mp hmem
        omega
      have hpermerase := hperm.erase (n + 1)
      rw [List.range'_concat] at hpermerase
      simp only [Nat.one_mul] at hpermerase
      rw [List.erase_append_right _ hnot] at hpermerase
      simpa [Nat.add_comm] using hpermerase
    have hparentlength : (q.filter (fun value => value ≤ n)).length = n := by
      simpa using hparentperm.length_eq
    have hparentmax : ∀ value ∈ q.filter (fun value => value ≤ n), value < n + 1 := by
      intro value hvalue
      have hle := (List.mem_filter.mp hvalue).2
      simp only [decide_eq_true_eq] at hle
      omega
    have hparentavoid : ¬ ContainsV2413 (q.filter (fun value => value ≤ n)) := by
      apply delete_maximum_avoids _ site (n + 1) (by omega) hparentmax
      rw [reconstruct]
      exact hq.2
    exact ⟨site, by omega, ⟨hparentperm, hparentavoid⟩, reconstruct.symm⟩
  
  induction n generalizing q with
  | zero =>
    have hlength : q.length = 0 := by simpa using hq.1.length_eq
    have hempty : q = [] := List.length_eq_zero_iff.mp hlength
    have hmzero : m = 0 := by omega
    subst q
    subst m
    simpa using hq
  | succ n ih =>
    by_cases heq : m = n + 1
    · have hfilter : q.filter (fun value => value ≤ m) = q := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hq.1.mem_iff.mp hvalue)
        simp only [decide_eq_true_eq]
        omega
      rw [hfilter]
      simpa [heq] using hq
    · obtain ⟨site, hsite, hparent, hrecover⟩ := maximum_parent n q hq
      have hsubset : m ≤ n := by omega
      have hrestricted := ih (q.filter (fun value => value ≤ n)) hparent hsubset
      rw [List.filter_filter] at hrestricted
      have hpred : (fun value : ℕ => decide (value ≤ m) && decide (value ≤ n)) =
          (fun value : ℕ => decide (value ≤ m)) := by
        funext value
        by_cases hvalue : value ≤ m
        · have hvalue' : value ≤ n := by omega
          simp [hvalue, hvalue']
        · simp [hvalue]
      rwa [hpred] at hrestricted

end D5.S3.Combinatorics.WeakAscent.WeakAscentPermParents
