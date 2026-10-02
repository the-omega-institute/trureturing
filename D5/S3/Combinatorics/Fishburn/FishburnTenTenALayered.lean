/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenALayered
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenALayered
   mirror-E: none(waiver:fishburn-a-layered-live-forms)
   anchors: []
   utility: none
   digest: A reversed interval between increasing blocks gives the T and E live forms. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenAMonotone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenALayered

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns FishburnTenTenAMonotone

set_option maxHeartbeats 1600000 in
theorem a_layered_forms (n low high : ℕ) (hgap : low + 2 ≤ high) (hhigh : high ≤ n) :
    let word := List.range' 1 low ++ (List.range' (low + 1) (high - low)).reverse ++
      List.range' (high + 1) (n - high)
    word ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ∧
      ∀ site, site ≤ n →
        (word.insertIdx site (n + 1) ∈
          avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
            site = 0 ∨ site = n ∨ high = n ∧ site = low) := by
  let form (size start finish : ℕ) :=
    List.range' 1 start ++ (List.range' (start + 1) (finish - start)).reverse ++
      List.range' (finish + 1) (size - finish)
  have hlen (size start finish : ℕ) (hs : start ≤ finish) (hf : finish ≤ size) :
      (form size start finish).length = size := by
    simp only [form, List.length_append, List.length_range', List.length_reverse]
    omega
  have hentry (size start finish index : ℕ) (hs : start ≤ finish) (hf : finish ≤ size)
      (hi : index < size) :
      (form size start finish).getD index 0 =
        if index < start then index + 1
        else if index < finish then start + finish - index else index + 1 := by
    dsimp only [form]
    rw [List.append_assoc]
    by_cases hleft : index < start
    · rw [List.getD_append _ _ _ _ (by simpa using hleft),
        List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
      simp only [hleft, ↓reduceIte, Nat.one_mul, Nat.add_comm]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_range']
      by_cases hmiddle : index < finish
      · rw [List.getD_append _ _ _ _ (by simp; omega),
          List.getD_reverse (index - start) (by simp; omega)]
        simp only [List.length_range']
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
        simp only [hleft, hmiddle, ↓reduceIte, Nat.one_mul]
        omega
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_reverse, List.length_range']
        rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
        simp only [hleft, hmiddle, ↓reduceIte, Nat.one_mul]
        omega
  have hslots (size start finish : ℕ) (hs : start + 2 ≤ finish) (hf : finish ≤ size)
      (hword : form size start finish ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
      (site : ℕ) (hsite : site ≤ size) :
      (form size start finish).insertIdx site (size + 1) ∈
        avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔
          site = 0 ∨ site = size ∨ finish = size ∧ site = start := by
    let word := form size start finish
    have hwlen : word.length = size := hlen size start finish (by omega) hf
    have he (index : ℕ) (hi : index < size) :=
      hentry size start finish index (by omega) hf hi
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
      by_cases hend : site = size
      · exact Or.inr (Or.inl hend)
      have hlegal : site ≤ start ∨ finish ≤ site := by
        by_contra hnot
        have hsafe := (hfish.mp hchild.2.1).2
        apply hsafe (site - 1) site (by omega) le_rfl (by omega)
        change (form size start finish).getD (site - 1) 0 =
          (form size start finish).getD site 0 + 1
        rw [he (site - 1) (by omega), he site (by omega)]
        split_ifs <;> omega
      have hge : start ≤ site := by
        by_contra hnot
        apply hchild.2.2 [1, 4, 2, 3] (by simp)
        apply h142.mpr
        right
        refine ⟨0, site, start, by omega, le_rfl, by omega, by omega, ?_, ?_⟩
        · change (form size start finish).getD 0 0 <
            (form size start finish).getD site 0
          rw [he 0 (by omega), he site (by omega)]
          split_ifs <;> omega
        · change (form size start finish).getD site 0 <
            (form size start finish).getD start 0
          rw [he site (by omega), he start (by omega)]
          split_ifs <;> omega
      have hfinish : finish = size := by
        by_contra hnot
        rcases hlegal with hleft | hright
        · have hsame : site = start := by omega
          apply hchild.2.2 [1, 4, 2, 3] (by simp)
          apply h142.mpr
          right
          refine ⟨0, finish - 1, finish, by omega, by omega, by omega,
            by omega, ?_, ?_⟩
          · change (form size start finish).getD 0 0 <
              (form size start finish).getD (finish - 1) 0
            rw [he 0 (by omega), he (finish - 1) (by omega)]
            split_ifs <;> omega
          · change (form size start finish).getD (finish - 1) 0 <
              (form size start finish).getD finish 0
            rw [he (finish - 1) (by omega), he finish (by omega)]
            split_ifs <;> omega
        · apply hchild.2.2 [2, 1, 4, 3] (by simp)
          apply h214.mpr
          right
          refine ⟨start, finish - 1, site, by omega, by omega, le_rfl,
            by omega, ?_, ?_⟩
          · change (form size start finish).getD (finish - 1) 0 <
              (form size start finish).getD start 0
            rw [he (finish - 1) (by omega), he start (by omega)]
            split_ifs <;> omega
          · change (form size start finish).getD start 0 <
              (form size start finish).getD site 0
            rw [he start (by omega), he site (by omega)]
            split_ifs <;> omega
      exact Or.inr (Or.inr ⟨hfinish, by rcases hlegal with hleft | hright <;> omega⟩)
    · intro hcuts
      refine ⟨?_, ?_, ?_⟩
      · apply (List.perm_insertIdx (size + 1) word (by omega)).trans
        apply (hword.1.cons (size + 1)).trans
        rw [List.range'_concat]
        simpa [Nat.add_comm] using
          (List.perm_append_comm (l₁ := [size + 1]) (l₂ := List.range' 1 size))
      · apply hfish.mpr
        refine ⟨hword.2.1, ?_⟩
        intro before later hb hl hn hbad
        have hnb : later < size := by omega
        change (form size start finish).getD before 0 =
          (form size start finish).getD later 0 + 1 at hbad
        rw [he before (by omega), he later hnb] at hbad
        rcases hcuts with hzero | hend | ⟨hfinish, hstart⟩
        · omega
        · omega
        · split_ifs at hbad <;> omega
      · intro pattern hpattern hocc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
        rcases hpattern with rfl | rfl | rfl
        · rcases h214.mp hocc with hocc |
            ⟨first, second, third, hfs, hs, ht, hn, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size start finish).getD second 0 <
              (form size start finish).getD first 0 at hlt
            rw [he second (by omega), he first (by omega)] at hlt
            rcases hcuts with hzero | hend | ⟨hfinish, hstart⟩
            · omega
            · omega
            · split_ifs at hlt <;> omega
        · rcases h142.mp hocc with hocc |
            ⟨first, second, third, hfsite, hs, hst, hn, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size start finish).getD second 0 <
              (form size start finish).getD third 0 at hgt
            rw [he second (by omega), he third (by omega)] at hgt
            rcases hcuts with hzero | hend | ⟨hfinish, hstart⟩
            · omega
            · omega
            · split_ifs at hgt <;> omega
        · rcases h312.mp hocc with hocc |
            ⟨first, second, third, hfs, hst, ht, hlt, hgt⟩
          · exact hword.2.2 _ (by simp) hocc
          · change (form size start finish).getD second 0 <
              (form size start finish).getD third 0 at hlt
            change (form size start finish).getD third 0 <
              (form size start finish).getD first 0 at hgt
            rw [he second (by omega), he third (by omega)] at hlt
            rw [he third (by omega), he first (by omega)] at hgt
            split_ifs at hlt hgt <;> omega
  have hmember : ∀ size start finish, start + 2 ≤ finish → finish ≤ size →
      form size start finish ∈
        avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro start finish hs hf
      by_cases hlast : finish = size
      · subst finish
        by_cases hzero : start = 0
        · subst start
          simpa only [form, List.range'_zero, List.nil_append, Nat.sub_zero,
            Nat.sub_self, List.append_nil] using (a_monotone_forms size).2.1
        have hinsert (parent : List ℕ) (hp : parent.length = size - 1)
            (he : ∀ index, index < size - 1 → parent.getD index 0 =
              if index < start then index + 1 else start + (size - 1) - index) :
            parent.insertIdx start size = form size start size := by
          apply List.ext_getElem
          · rw [List.length_insertIdx_of_le_length (by omega),
              hlen size start size (by omega) le_rfl, hp]
            omega
          · intro index hi hj
            have hib : index < size := by
              rwa [hlen size start size (by omega) le_rfl] at hj
            rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj,
              hentry size start size index (by omega) le_rfl hib]
            rcases lt_trichotomy index start with hleft | heq | hright
            · rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_of_lt hleft,
                ← List.getD_eq_getElem _ 0 (by omega), he index (by omega)]
              simp only [hleft, ↓reduceIte]
            · subst index
              rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_self]
              split_ifs <;> omega
            · rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_of_gt hright,
                ← List.getD_eq_getElem _ 0 (by omega), he (index - 1) (by omega)]
              split_ifs <;> omega
        by_cases hbase : size = start + 2
        · have hp : (List.range' 1 (size - 1)).length = size - 1 := List.length_range'
          have heq := hinsert (List.range' 1 (size - 1)) hp (by
            intro index hi
            rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
            simp only [Nat.one_mul]
            split_ifs <;> omega)
          have hchild := (((a_monotone_forms (size - 1)).2.2 start (by omega)).1).mpr
            (Or.inr (by omega))
          have hvalue : size - 1 + 1 = size := by omega
          rw [hvalue, heq] at hchild
          exact hchild
        · have hsold : start + 2 ≤ size - 1 := by omega
          have hparent := ih (size - 1) (by omega) start (size - 1) hsold le_rfl
          have heq := hinsert (form (size - 1) start (size - 1))
            (hlen _ _ _ (by omega) le_rfl) (by
              intro index hi
              rw [hentry (size - 1) start (size - 1) index (by omega) le_rfl hi]
              simp only [hi, ↓reduceIte])
          have hchild := (hslots (size - 1) start (size - 1) hsold le_rfl hparent
            start (by omega)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))
          have hvalue : size - 1 + 1 = size := by omega
          rw [hvalue, heq] at hchild
          exact hchild
      · have hfold : finish ≤ size - 1 := by omega
        have hparent := ih (size - 1) (by omega) start finish hs hfold
        have hchild := (hslots (size - 1) start finish hs hfold hparent
          (size - 1) le_rfl).mpr (Or.inr (Or.inl rfl))
        have heq : (form (size - 1) start finish).insertIdx (size - 1) size =
            form size start finish := by
          have hp := hlen (size - 1) start finish (by omega) hfold
          apply List.ext_getElem
          · rw [List.length_insertIdx_of_le_length (by omega),
              hlen size start finish (by omega) hf, hp]
            omega
          · intro index hi hj
            have hib : index < size := by
              rwa [hlen size start finish (by omega) hf] at hj
            rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj,
              hentry size start finish index (by omega) hf hib]
            by_cases hbefore : index < size - 1
            · rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_of_lt hbefore,
                ← List.getD_eq_getElem _ 0 (by omega),
                hentry (size - 1) start finish index (by omega) hfold hbefore]
            · have heq : index = size - 1 := by omega
              subst index
              rw [List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_self]
              split_ifs <;> omega
        have hvalue : size - 1 + 1 = size := by omega
        rw [hvalue, heq] at hchild
        exact hchild
  have hword := hmember n low high hgap hhigh
  exact ⟨hword, hslots n low high hgap hhigh hword⟩

end D5.S3.Combinatorics.Fishburn.FishburnTenTenALayered
