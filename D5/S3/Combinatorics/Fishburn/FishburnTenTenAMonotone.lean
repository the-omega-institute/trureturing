/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenAMonotone
   mirror-E: none(waiver:fishburn-a-monotone-live-forms)
   anchors: []
   utility: none
   digest: Increasing and decreasing live forms have exactly their specified active cuts. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasic2143
import D5.S3.Combinatorics.Fishburn.FishburnBasicPatterns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenAMonotone

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns

set_option maxHeartbeats 1200000 in
theorem a_monotone_forms (n : ℕ) :
    List.range' 1 n ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
    (List.range' 1 n).reverse ∈
      avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
    ∀ site, site ≤ n →
      ((List.range' 1 n).insertIdx site (n + 1) ∈
        avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ n ≤ site + 1) ∧
      (((List.range' 1 n).reverse).insertIdx site (n + 1) ∈
        avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ site = n) := by
  have hsites (size : ℕ)
      (hinc : List.range' 1 size ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
      (hdec : (List.range' 1 size).reverse ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
      (site : ℕ) (hsite : site ≤ size) :
      ((List.range' 1 size).insertIdx site (size + 1) ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ size ≤ site + 1) ∧
      (((List.range' 1 size).reverse).insertIdx site (size + 1) ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ site = size) := by
    have hientry (index : ℕ) (hi : index < size) :
        (List.range' 1 size).getD index 0 = index + 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
      simp only [Nat.one_mul, Nat.add_comm]
    have hdentry (index : ℕ) (hi : index < size) :
        ((List.range' 1 size).reverse).getD index 0 = size - index := by
      rw [List.getD_reverse index (by simpa using hi)]
      simp only [List.length_range']
      rw [hientry (size - 1 - index) (by omega)]
      omega
    have hbuild (word : List ℕ)
        (hword : word ∈
          avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
        (hsafe : ∀ before later, before + 1 = site → site ≤ later → later < size →
          word.getD before 0 ≠ word.getD later 0 + 1)
        (h214 : ∀ first second third, first < second → second < site → site ≤ third →
          third < size → ¬ (word.getD second 0 < word.getD first 0 ∧
            word.getD first 0 < word.getD third 0))
        (h142 : ∀ first second third, first < site → site ≤ second → second < third →
          third < size → ¬ (word.getD first 0 < word.getD second 0 ∧
            word.getD second 0 < word.getD third 0))
        (h312 : ∀ first second third, first < second → second < third → third < site →
          ¬ (word.getD second 0 < word.getD third 0 ∧
            word.getD third 0 < word.getD first 0)) :
        word.insertIdx site (size + 1) ∈
          avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      have hlen : word.length = size := by simpa using hword.1.length_eq
      have hmax (value : ℕ) (hv : value ∈ word) : value < size + 1 := by
        have hrange := hword.1.mem_iff.mp hv
        simp only [List.mem_range'_1] at hrange
        omega
      refine ⟨?_, ?_, ?_⟩
      · apply (List.perm_insertIdx (size + 1) word (by omega)).trans
        apply (hword.1.cons (size + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      · apply (isFishburn_insertIdx_max_iff word (size + 1) site (by omega) hmax).mpr
        exact ⟨hword.2.1, by simpa only [hlen] using hsafe⟩
      · intro pattern hpattern hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl
        · rcases (maximum_2143_test size word hword.1 site (by omega)).mp hocc with
            hocc | ⟨first, second, third, hfs, hs, ht, hb, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · exact h214 first second third hfs hs ht (by omega) ⟨hlt, hgt⟩
        · rcases (maximum_pattern_tests size word hword.1 site (by omega)).2.2.mp
            hocc with hocc | ⟨first, second, third, hf, hs, hst, hb, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · exact h142 first second third hf hs hst (by omega) ⟨hlt, hgt⟩
        · rcases (maximum_pattern_tests size word hword.1 site (by omega)).2.1.mp
            hocc with hocc | ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · exact h312 first second third hfs hst ht ⟨hlt, hgt⟩
    constructor
    · constructor
      · intro hchild
        by_cases hzero : site = 0
        · exact Or.inl hzero
        · right
          by_contra hnot
          have hbound : site + 1 < size := by omega
          apply hchild.2.2 [1, 4, 2, 3] (by simp)
          apply (maximum_pattern_tests size _ hinc.1 site (by simp; omega)).2.2.mpr
          right
          refine ⟨0, site, site + 1, by omega, le_rfl, by omega,
            by simp; omega, ?_, ?_⟩
          · rw [hientry 0 (by omega), hientry site (by omega)]
            omega
          · rw [hientry site (by omega), hientry (site + 1) hbound]
            omega
      · intro hcuts
        refine hbuild _ hinc ?_ ?_ ?_ ?_
        · intro before later hb hl hn
          rw [hientry before (by omega), hientry later hn]
          omega
        · intro first second third hfs hs ht hn hbad
          rw [hientry second (by omega), hientry first (by omega)] at hbad
          omega
        · intro first second third hf hs hst hn _
          rcases hcuts with hzero | hend <;> omega
        · intro first second third hfs hst ht hbad
          rw [hientry third (by omega), hientry first (by omega)] at hbad
          omega
    · constructor
      · intro hchild
        by_cases hzero : site = 0
        · exact Or.inl hzero
        · right
          by_contra hnot
          have hlt : site < size := by omega
          have hmax (value : ℕ) (hv : value ∈ (List.range' 1 size).reverse) :
              value < size + 1 := by
            have hrange := hdec.1.mem_iff.mp hv
            simp only [List.mem_range'_1] at hrange
            omega
          have hsafe := ((isFishburn_insertIdx_max_iff _ (size + 1) site
            (by simp; omega) hmax).mp hchild.2.1).2
          apply hsafe (site - 1) site (by omega) le_rfl (by simp; omega)
          rw [hdentry (site - 1) (by omega), hdentry site hlt]
          omega
      · intro hcuts
        refine hbuild _ hdec ?_ ?_ ?_ ?_
        · intro before later hb hl hn
          rcases hcuts with hzero | hend <;> omega
        · intro first second third hfs hs ht hn hbad
          rw [hdentry first (by omega), hdentry third hn] at hbad
          omega
        · intro first second third hf hs hst hn hbad
          rw [hdentry second (by omega), hdentry third hn] at hbad
          omega
        · intro first second third hfs hst ht hbad
          rw [hdentry second (by omega), hdentry third (by omega)] at hbad
          omega
  induction n with
  | zero =>
    have hempty : [] ∈ avoiders 0 [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      refine ⟨by simp, ?_, ?_⟩
      · intro first second hfs hs
        simp at hs
      · intro pattern hpattern hocc
        obtain ⟨values, _, _, hsublist, _⟩ := hocc
        have hlength := hsublist.length_le
        simp only [List.length_map, List.length_nil] at hlength
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl <;> simp at hlength
    have hinc : List.range' 1 0 ∈
        avoiders 0 [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      simpa using hempty
    have hdec : (List.range' 1 0).reverse ∈
        avoiders 0 [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      simpa using hempty
    exact ⟨hinc, hdec, hsites 0 hinc hdec⟩
  | succ size ih =>
    have hinc : List.range' 1 (size + 1) ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      have hchild := ((ih.2.2 size le_rfl).1).mpr (Or.inr (by omega))
      have hinsert : (List.range' 1 size).insertIdx size (size + 1) =
          List.range' 1 size ++ [size + 1] := by
        simpa only [List.length_range'] using
          (List.insertIdx_length_self (l := List.range' 1 size) (x := size + 1))
      rw [hinsert] at hchild
      simpa only [List.length_range', List.range'_concat, Nat.one_mul,
        Nat.add_comm] using hchild
    have hdec : (List.range' 1 (size + 1)).reverse ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
      have hchild := ((ih.2.2 0 (by omega)).2).mpr (Or.inl rfl)
      simpa only [List.insertIdx_zero, List.range'_concat, Nat.one_mul,
        List.reverse_append, List.reverse_singleton, List.singleton_append,
        Nat.add_comm] using hchild
    exact ⟨hinc, hdec, hsites (size + 1) hinc hdec⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTenAMonotone
