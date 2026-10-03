/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenAValley
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenAValley
   mirror-E: none(waiver:fishburn-a-valley-live-forms)
   anchors: []
   utility: none
   digest: The U and V forms are reconstructed inductively and have one positive active cut. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenALayered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenAValley

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns FishburnTenTenAMonotone
open FishburnTenTenALayered

set_option maxHeartbeats 2400000 in
theorem a_valley_forms (n bottom peak : ℕ) (hbottom : 2 ≤ bottom)
    (hpeak : bottom < peak) (hsize : peak ≤ n) :
    let word := (List.range' (bottom + 1) (peak - bottom)).reverse ++ [1] ++
      List.range' (peak + 1) (n - peak) ++ (List.range' 2 (bottom - 1)).reverse
    word ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
      ∀ site, site ≤ n →
        (word.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
            site = 0 ∨ site = n - bottom + 1) := by
  let form (size lower upper : ℕ) :=
    (List.range' (lower + 1) (upper - lower)).reverse ++ [1] ++
      List.range' (upper + 1) (size - upper) ++ (List.range' 2 (lower - 1)).reverse
  have hlen (size lower upper : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ size) : (form size lower upper).length = size := by
    simp only [form, List.length_append, List.length_range', List.length_reverse,
      List.length_cons, List.length_nil]
    omega
  have hentry (size lower upper index : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ size) (hi : index < size) :
      (form size lower upper).getD index 0 =
        if index < upper - lower then upper - index
        else if index = upper - lower then 1
        else if index < size - lower + 1 then index + lower else size - index + 1 := by
    dsimp only [form]
    simp only [List.append_assoc, List.cons_append]
    by_cases hleft : index < upper - lower
    · rw [List.getD_append _ _ _ _ (by simp; omega),
        List.getD_reverse index (by simp; omega)]
      simp only [List.length_range']
      rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
      simp only [hleft, ↓reduceIte, Nat.one_mul]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_reverse, List.length_range']
      by_cases hone : index = upper - lower
      · subst index
        simp
      · have hsub : index - (upper - lower) = (index - (upper - lower) - 1) + 1 := by
          omega
        rw [hsub, List.getD_cons_succ]
        simp only [List.nil_append]
        by_cases hmiddle : index < size - lower + 1
        · rw [List.getD_append _ _ _ _ (by simp; omega),
            List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
          simp only [hleft, hone, hmiddle, ↓reduceIte, Nat.one_mul]
          omega
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_range']
          rw [List.getD_reverse _ (by simp; omega)]
          simp only [List.length_range']
          rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
          simp only [hleft, hone, hmiddle, ↓reduceIte, Nat.one_mul]
          omega
  have hslots (size lower upper : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ size) (hword : form size lower upper ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
      (site : ℕ) (hsite : site ≤ size) :
      (form size lower upper).insertIdx site (size + 1) ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ site = size - lower + 1 := by
    let word := form size lower upper
    have hwlen : word.length = size := hlen size lower upper hl hu hs
    have he (index : ℕ) (hi : index < size) := hentry size lower upper index hl hu hs hi
    have hmax (value : ℕ) (hv : value ∈ word) : value < size + 1 := by
      have hm := hword.1.mem_iff.mp hv
      simp only [List.mem_range'_1] at hm
      omega
    have hfish := isFishburn_insertIdx_max_iff word (size + 1) site (by omega) hmax
    have h214 := maximum_2143_test size word hword.1 site (by omega)
    have h142 := (maximum_pattern_tests size word hword.1 site (by omega)).2.2
    have h312 := (maximum_pattern_tests size word hword.1 site (by omega)).2.1
    change word.insertIdx site (size + 1) ∈ _ ↔ _
    constructor
    · intro hchild
      by_cases hzero : site = 0
      · exact Or.inl hzero
      right
      have hsafe := (hfish.mp hchild.2.1).2
      have hafterone : upper - lower < site := by
        by_contra hnot
        by_cases hone : site = upper - lower
        · apply hsafe (site - 1) (size - lower + 1) (by omega) (by omega) (by omega)
          change (form size lower upper).getD (site - 1) 0 =
            (form size lower upper).getD (size - lower + 1) 0 + 1
          rw [he (site - 1) (by omega), he (size - lower + 1) (by omega)]
          split_ifs <;> omega
        · apply hsafe (site - 1) site (by omega) le_rfl (by omega)
          change (form size lower upper).getD (site - 1) 0 =
            (form size lower upper).getD site 0 + 1
          rw [he (site - 1) (by omega), he site (by omega)]
          split_ifs <;> omega
      have hbeforeend : site < size := by
        by_contra hnot
        have hend : site = size := by omega
        apply hchild.2.2 [3, 1, 2, 4] (by simp)
        apply h312.mpr
        right
        refine ⟨0, upper - lower, size - 1, by omega, by omega, by omega, ?_, ?_⟩
        · change (form size lower upper).getD (upper - lower) 0 <
            (form size lower upper).getD (size - 1) 0
          rw [he (upper - lower) (by omega), he (size - 1) (by omega)]
          split_ifs <;> omega
        · change (form size lower upper).getD (size - 1) 0 <
            (form size lower upper).getD 0 0
          rw [he (size - 1) (by omega), he 0 (by omega)]
          split_ifs <;> omega
      have hcutupper : site ≤ size - lower + 1 := by
        by_contra hnot
        apply hsafe (site - 1) site (by omega) le_rfl (by omega)
        change (form size lower upper).getD (site - 1) 0 =
          (form size lower upper).getD site 0 + 1
        rw [he (site - 1) (by omega), he site (by omega)]
        split_ifs <;> omega
      by_contra hnot
      apply hchild.2.2 [2, 1, 4, 3] (by simp)
      apply h214.mpr
      right
      refine ⟨0, upper - lower, site, by omega, hafterone, le_rfl,
        by omega, ?_, ?_⟩
      · change (form size lower upper).getD (upper - lower) 0 <
          (form size lower upper).getD 0 0
        rw [he (upper - lower) (by omega), he 0 (by omega)]
        split_ifs <;> omega
      · change (form size lower upper).getD 0 0 <
          (form size lower upper).getD site 0
        rw [he 0 (by omega), he site (by omega)]
        split_ifs <;> omega
    · intro hcuts
      refine ⟨?_, ?_, ?_⟩
      · apply (List.perm_insertIdx (size + 1) word (by omega)).trans
        apply (hword.1.cons (size + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      · apply hfish.mpr
        refine ⟨hword.2.1, ?_⟩
        intro before later hb hlater hn hbad
        change (form size lower upper).getD before 0 =
          (form size lower upper).getD later 0 + 1 at hbad
        rw [he before (by omega), he later (by omega)] at hbad
        rcases hcuts with hzero | hcut
        · omega
        · split_ifs at hbad <;> omega
      · intro pattern hpattern hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl
        · rcases h214.mp hocc with hocc |
            ⟨first, second, third, hfs, hslt, ht, hn, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size lower upper).getD second 0 <
              (form size lower upper).getD first 0 at hlt
            change (form size lower upper).getD first 0 <
              (form size lower upper).getD third 0 at hgt
            rw [he second (by omega), he first (by omega)] at hlt
            rw [he first (by omega), he third (by omega)] at hgt
            rcases hcuts with hzero | hcut
            · omega
            · split_ifs at hlt hgt <;> omega
        · rcases h142.mp hocc with hocc |
            ⟨first, second, third, hfsite, hssite, hst, hn, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size lower upper).getD second 0 <
              (form size lower upper).getD third 0 at hgt
            rw [he second (by omega), he third (by omega)] at hgt
            rcases hcuts with hzero | hcut
            · omega
            · split_ifs at hgt <;> omega
        · rcases h312.mp hocc with hocc |
            ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size lower upper).getD second 0 <
              (form size lower upper).getD third 0 at hlt
            change (form size lower upper).getD third 0 <
              (form size lower upper).getD first 0 at hgt
            rw [he second (by omega), he third (by omega)] at hlt
            rw [he third (by omega), he first (by omega)] at hgt
            rcases hcuts with hzero | hcut
            · omega
            · split_ifs at hlt hgt <;> omega
  have hprepend (size : ℕ) (parent : List ℕ)
      (hp : parent ∈ avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]) :
      (size + 1) :: parent ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
    have hmax (value : ℕ) (hv : value ∈ parent) : value < size + 1 := by
      have hm := hp.1.mem_iff.mp hv
      simp only [List.mem_range'_1] at hm
      omega
    refine ⟨?_, ?_, ?_⟩
    · apply (hp.1.cons (size + 1)).trans
      rw [List.range'_concat]
      simpa [Nat.add_comm] using
        (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
    · apply (isFishburn_insertIdx_max_iff parent (size + 1) 0 (by omega) hmax).mpr
      exact ⟨hp.2.1, by intro before later hb; omega⟩
    · intro pattern hpattern hocc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl
      · have hh := (maximum_2143_test size parent hp.1 0 (by omega)).mp hocc
        rcases hh with hh | ⟨_, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · have hh := (maximum_pattern_tests size parent hp.1 0 (by omega)).2.2.mp hocc
        rcases hh with hh | ⟨_, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · have hh := (maximum_pattern_tests size parent hp.1 0 (by omega)).2.1.mp hocc
        rcases hh with hh | ⟨_, _, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
  have hmember : ∀ size lower upper, 2 ≤ lower → lower < upper → upper ≤ size →
      form size lower upper ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro lower upper hl hu hs
      by_cases hlast : upper = size
      · subst upper
        by_cases hbase : size = lower + 1
        · have hp : 1 :: (List.range' 2 (lower - 1)).reverse ∈
              avoiders lower [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
            by_cases htwo : lower = 2
            · subst lower
              exact (a_monotone_forms 2).1
            · have hh := (a_layered_forms lower 1 lower (by omega) le_rfl).1
              simpa only [List.range'_one, Nat.sub_self, List.range'_zero,
                List.append_nil, List.singleton_append] using hh
          have hh := hprepend lower _ hp
          have hdiff : lower + 1 - lower = 1 := by omega
          simpa only [form, hbase, hdiff, List.range'_one, Nat.sub_self,
            List.range'_zero, List.reverse_singleton, List.append_nil,
            List.singleton_append, List.cons_append, List.nil_append] using hh
        · have huold : lower < size - 1 := by omega
          have hp := ih (size - 1) (by omega) lower (size - 1) hl huold le_rfl
          have hh := (hslots (size - 1) lower (size - 1) hl huold le_rfl hp
            0 (by omega)).mpr (Or.inl rfl)
          have heq : (form (size - 1) lower (size - 1)).insertIdx 0 size =
              form size lower size := by
            apply List.ext_getElem
            · rw [List.length_insertIdx_of_le_length (by omega),
                hlen _ _ _ hl huold le_rfl, hlen _ _ _ hl hu le_rfl]
              omega
            · intro index hi hj
              have hib : index < size := by rwa [hlen _ _ _ hl hu le_rfl] at hj
              rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj,
                hentry size lower size index hl hu le_rfl hib]
              by_cases hzero : index = 0
              · subst index
                rw [List.insertIdx_zero, List.getD_cons_zero]
                split_ifs <;> omega
              · rw [List.getD_eq_getElem _ 0 hi,
                  List.getElem_insertIdx_of_gt (by omega : 0 < index),
                  ← List.getD_eq_getElem _ 0 (by
                    rw [hlen _ _ _ hl huold le_rfl]; omega),
                  hentry (size - 1) lower (size - 1) (index - 1) hl huold le_rfl
                    (by omega)]
                split_ifs <;> omega
          have hvalue : size - 1 + 1 = size := by omega
          rw [hvalue, heq] at hh
          exact hh
      · have hsold : upper ≤ size - 1 := by omega
        have hp := ih (size - 1) (by omega) lower upper hl hu hsold
        have hh := (hslots (size - 1) lower upper hl hu hsold hp (size - lower)
          (by omega)).mpr (Or.inr (by omega))
        have heq : (form (size - 1) lower upper).insertIdx (size - lower) size =
            form size lower upper := by
          have hparentlen := hlen (size - 1) lower upper hl hu hsold
          apply List.ext_getElem
          · rw [List.length_insertIdx_of_le_length (by omega), hparentlen,
              hlen _ _ _ hl hu hs]
            omega
          · intro index hi hj
            have hib : index < size := by rwa [hlen _ _ _ hl hu hs] at hj
            rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj,
              hentry size lower upper index hl hu hs hib]
            rcases lt_trichotomy index (size - lower) with hleft | hequal | hright
            · rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_of_lt hleft,
                ← List.getD_eq_getElem _ 0 (by omega),
                hentry (size - 1) lower upper index hl hu hsold (by omega)]
              split_ifs <;> omega
            · subst index
              rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_self]
              split_ifs <;> omega
            · rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_of_gt hright,
                ← List.getD_eq_getElem _ 0 (by omega),
                hentry (size - 1) lower upper (index - 1) hl hu hsold (by omega)]
              split_ifs <;> omega
        have hvalue : size - 1 + 1 = size := by omega
        rw [hvalue, heq] at hh
        exact hh
  have hword := hmember n bottom peak hbottom hpeak hsize
  exact ⟨hword, hslots n bottom peak hbottom hpeak hsize hword⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTenAValley
