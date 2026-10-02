/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenTenATree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenTenATree
   mirror-E: none(waiver:fishburn-a-exhaustive-maximum-deletion)
   anchors: []
   utility: none
   digest: Maximum deletion classifies every A node into explicit live forms or a terminal node. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenTenAValley
import D5.S3.Combinatorics.Fishburn.FishburnBasicParents
import D5.S3.Combinatorics.Fishburn.FishburnBasicPrepend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenTenATree

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasic2143 FishburnBasicPatterns FishburnBasicParents FishburnBasicPrepend
open FishburnTenTenAMonotone FishburnTenTenALayered FishburnTenTenAValley

set_option maxHeartbeats 3200000 in
theorem a_classification (n : ℕ) (hsize : 2 ≤ n) (p : List ℕ)
    (hp : p ∈ avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]) :
    p = List.range' 1 n ∨
    (∃ low high, low + 2 ≤ high ∧ high ≤ n ∧
      p = List.range' 1 low ++ (List.range' (low + 1) (high - low)).reverse ++
        List.range' (high + 1) (n - high)) ∨
    (∃ bottom peak, 2 ≤ bottom ∧ bottom < peak ∧ peak ≤ n ∧
      p = (List.range' (bottom + 1) (peak - bottom)).reverse ++ [1] ++
        List.range' (peak + 1) (n - peak) ++ (List.range' 2 (bottom - 1)).reverse) ∨
    (∀ site, site ≤ n →
      (p.insertIdx site (n + 1) ∈
        avoiders (n + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔ site = 0)) := by
  let layered (size start finish : ℕ) :=
    List.range' 1 start ++ (List.range' (start + 1) (finish - start)).reverse ++
      List.range' (finish + 1) (size - finish)
  let valley (size lower upper : ℕ) :=
    (List.range' (lower + 1) (upper - lower)).reverse ++ [1] ++
      List.range' (upper + 1) (size - upper) ++ (List.range' 2 (lower - 1)).reverse
  have hllen (size start finish : ℕ) (hs : start ≤ finish) (hf : finish ≤ size) :
      (layered size start finish).length = size := by
    simp only [layered, List.length_append, List.length_range', List.length_reverse]
    omega
  have hvlen (size lower upper : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ size) : (valley size lower upper).length = size := by
    simp only [valley, List.length_append, List.length_range', List.length_reverse,
      List.length_cons, List.length_nil]
    omega
  have hie (size index : ℕ) (hi : index < size) :
      (List.range' 1 size).getD index 0 = index + 1 := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_range']
    simp only [Nat.one_mul, Nat.add_comm]
  have hle (size start finish index : ℕ) (hs : start ≤ finish) (hf : finish ≤ size)
      (hi : index < size) :
      (layered size start finish).getD index 0 =
        if index < start then index + 1
        else if index < finish then start + finish - index else index + 1 := by
    dsimp only [layered]
    rw [List.append_assoc]
    by_cases hleft : index < start
    · rw [List.getD_append _ _ _ _ (by simp; omega),
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
  have hve (size lower upper index : ℕ) (hl : 2 ≤ lower) (hu : lower < upper)
      (hs : upper ≤ size) (hi : index < size) :
      (valley size lower upper).getD index 0 =
        if index < upper - lower then upper - index
        else if index = upper - lower then 1
        else if index < size - lower + 1 then index + lower else size - index + 1 := by
    dsimp only [valley]
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
  have hinsert (size : ℕ) (parent child : List ℕ) (site : ℕ)
      (hp : parent.length = size) (hc : child.length = size + 1) (hs : site ≤ size)
      (hbefore : ∀ index, index < site → child.getD index 0 = parent.getD index 0)
      (hat : child.getD site 0 = size + 1)
      (hafter : ∀ index, site < index → index < size + 1 →
        child.getD index 0 = parent.getD (index - 1) 0) :
      parent.insertIdx site (size + 1) = child := by
    apply List.ext_getElem
    · rw [List.length_insertIdx_of_le_length (by omega), hp, hc]
    · intro index hi hj
      rw [← List.getD_eq_getElem _ 0 hi, ← List.getD_eq_getElem _ 0 hj]
      rcases lt_trichotomy index site with hlt | heq | hgt
      · rw [hbefore index hlt, List.getD_eq_getElem _ 0 hi,
          List.getElem_insertIdx_of_lt hlt, List.getD_eq_getElem _ 0 (by omega)]
      · subst index
        rw [hat, List.getD_eq_getElem _ 0 hi, List.getElem_insertIdx_self]
      · rw [hafter index hgt (by omega), List.getD_eq_getElem _ 0 hi,
          List.getElem_insertIdx_of_gt hgt, List.getD_eq_getElem _ 0 (by omega)]
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
      · rcases (maximum_2143_test size parent hp.1 0 (by omega)).mp hocc with
          hh | ⟨_, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · rcases (maximum_pattern_tests size parent hp.1 0 (by omega)).2.2.mp hocc with
          hh | ⟨_, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
      · rcases (maximum_pattern_tests size parent hp.1 0 (by omega)).2.1.mp hocc with
          hh | ⟨_, _, _, _, _, hlt, _⟩
        · exact hp.2.2 _ (by simp) hh
        · omega
  have hterminal (size : ℕ) (hsize : 1 ≤ size) (parent : List ℕ)
      (hp : parent ∈ avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]])
      (hkill : ∀ cut, cut ≠ 0 → cut ≤ size →
        parent.insertIdx cut (size + 1) ∈
          avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] →
        ∃ first second, first < second ∧ second < cut ∧
          parent.getD first 0 < parent.getD second 0) :
      ∀ site, site ≤ size + 1 →
        (((size + 1) :: parent).insertIdx site (size + 2) ∈
          avoiders (size + 2) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔ site = 0) := by
    intro site hs
    constructor
    · intro hchild
      by_contra hnonzero
      have hlen : parent.length = size := by simpa using hp.1.length_eq
      have hpatterns : ∀ pattern ∈ [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]],
          pattern = [1, 3, 2, 4] ∨ pattern = [2, 1, 4, 3] ∨
            pattern = [1, 4, 2, 3] ∨ pattern = [3, 1, 2, 4] := by
        intro pattern hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl <;> simp
      have hsite : site - 1 + 1 = site := by omega
      have hh := (prepend_inherited_sites size parent hsize hp.1 hp.2.1
        [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] hpatterns (site - 1)
        (by omega)).mp (by simpa only [hsite] using hchild)
      obtain ⟨first, second, hfs, hsc, hlt⟩ := hkill (site - 1) hh.1 (by omega) hh.2.1
      have hgt := hh.2.2 (by simp) first second hfs hsc
      omega
    · intro heq
      subst site
      simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
        hprepend (size + 1) _ (hprepend size parent hp)
  have hclass : ∀ size, 2 ≤ size → ∀ word,
      word ∈ avoiders size [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] →
      word = List.range' 1 size ∨
      (∃ start finish, start + 2 ≤ finish ∧ finish ≤ size ∧
        word = layered size start finish) ∨
      (∃ lower upper, 2 ≤ lower ∧ lower < upper ∧ upper ≤ size ∧
        word = valley size lower upper) ∨
      (∀ site, site ≤ size →
        (word.insertIdx site (size + 1) ∈
          avoiders (size + 1) [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]] ↔ site = 0)) := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro hsize word hword
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
      obtain ⟨entry, hentry⟩ := (maximum_insertion_bijection m
        [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]).2 ⟨word, hword⟩
      have heq : entry.val.1.insertIdx entry.val.2 (m + 1) = word :=
        congrArg Subtype.val hentry
      rcases entry with ⟨⟨parent, site⟩, hparent, hsite, hactive⟩
      dsimp only at hparent hsite hactive heq
      subst word
      have hplen : parent.length = m := by simpa using hparent.1.length_eq
      have hs : site ≤ m := by omega
      by_cases hsmall : m = 1
      · have hperm : parent.Perm [1] := by
          simpa only [hsmall, List.range'_one] using hparent.1
        have hpone : parent = [1] := List.perm_singleton.mp hperm
        rw [hsmall]
        subst parent
        have hcuts : site = 0 ∨ site = 1 := by omega
        rcases hcuts with rfl | rfl
        · right; left
          exact ⟨0, 2, by omega, le_rfl, rfl⟩
        · left
          rfl
      have hm : 2 ≤ m := by omega
      rcases ih m (by omega) hm parent hparent with hinc | hlayer | hvalley | hterm
      · subst parent
        have hcuts := ((a_monotone_forms m).2.2 site hs).1.mp hactive
        rcases hcuts with hzero | hlast
        · subst site
          by_cases htwo : m = 2
          · subst m
            right; right; left
            exact ⟨2, 3, le_rfl, by omega, le_rfl, rfl⟩
          · right; right; right
            simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
              hterminal m (by omega) _ hparent (by
                intro cut hn hc ha
                have hh := ((a_monotone_forms m).2.2 cut hc).1.mp ha
                have hk : 2 ≤ cut := by rcases hh with hz | he <;> omega
                refine ⟨0, 1, by omega, by omega, ?_⟩
                rw [hie m 0 (by omega), hie m 1 (by omega)]
                omega)
        · by_cases he : site = m
          · subst site
            left
            apply hinsert m _ _ m (by simp) (by simp) le_rfl
            · intro index hi
              rw [hie (m + 1) index (by omega), hie m index hi]
            · rw [hie (m + 1) m (by omega)]
            · intro index hi hb
              omega
          · have hcut : site = m - 1 := by omega
            subst site
            right; left
            refine ⟨m - 1, m + 1, by omega, le_rfl, ?_⟩
            apply hinsert m _ _ (m - 1) (by simp)
              (hllen _ _ _ (by omega) le_rfl) (by omega)
            · intro index hi
              rw [hle (m + 1) (m - 1) (m + 1) index (by omega) le_rfl (by omega),
                hie m index (by omega)]
              split_ifs <;> omega
            · rw [hle (m + 1) (m - 1) (m + 1) (m - 1) (by omega) le_rfl (by omega)]
              split_ifs <;> omega
            · intro index hi hb
              rw [hle (m + 1) (m - 1) (m + 1) index (by omega) le_rfl hb,
                hie m (index - 1) (by omega)]
              split_ifs <;> omega
      · obtain ⟨start, finish, hgap, hf, rfl⟩ := hlayer
        have hcuts := (a_layered_forms m start finish hgap hf).2 site hs |>.mp hactive
        rcases hcuts with hzero | hend | ⟨hfinish, hstart⟩
        · subst site
          by_cases hfinish : finish = m
          · subst finish
            by_cases hstart : start = 0
            · subst start
              right; left
              refine ⟨0, m + 1, by omega, le_rfl, ?_⟩
              apply hinsert m _ _ 0 (hllen _ _ _ (by omega) le_rfl)
                (hllen _ _ _ (by omega) le_rfl) (by omega)
              · intro index hi
                omega
              · rw [hle (m + 1) 0 (m + 1) 0 (by omega) le_rfl (by omega)]
                simp
              · intro index hi hb
                rw [hle (m + 1) 0 (m + 1) index (by omega) le_rfl hb,
                  hle m 0 m (index - 1) (by omega) le_rfl (by omega)]
                split_ifs <;> omega
            · by_cases hone : start = 1
              · subst start
                right; right; left
                refine ⟨m, m + 1, by omega, by omega, le_rfl, ?_⟩
                apply hinsert m _ _ 0 (hllen _ _ _ (by omega) le_rfl)
                  (hvlen _ _ _ (by omega) (by omega) le_rfl) (by omega)
                · intro index hi
                  omega
                · rw [hve (m + 1) m (m + 1) 0 (by omega) (by omega) le_rfl (by omega)]
                  simp
                · intro index hi hb
                  rw [hve (m + 1) m (m + 1) index (by omega) (by omega) le_rfl hb,
                    hle m 1 m (index - 1) (by omega) le_rfl (by omega)]
                  split_ifs <;> omega
              · right; right; right
                simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
                  hterminal m (by omega) _ hparent (by
                    intro cut hn hc ha
                    have hh := (a_layered_forms m start m hgap le_rfl).2 cut hc |>.mp ha
                    have hk : 2 ≤ cut := by rcases hh with hz | he | hh <;> omega
                    refine ⟨0, 1, by omega, by omega, ?_⟩
                    rw [hle m start m 0 (by omega) le_rfl (by omega),
                      hle m start m 1 (by omega) le_rfl (by omega)]
                    split_ifs <;> omega)
          · right; right; right
            simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
              hterminal m (by omega) _ hparent (by
                intro cut hn hc ha
                have hh := (a_layered_forms m start finish hgap hf).2 cut hc |>.mp ha
                have hcut : cut = m := by rcases hh with hz | he | hh <;> omega
                refine ⟨finish - 1, finish, by omega, by omega, ?_⟩
                rw [hle m start finish (finish - 1) (by omega) hf (by omega),
                  hle m start finish finish (by omega) hf (by omega)]
                split_ifs <;> omega)
        · subst site
          right; left
          refine ⟨start, finish, hgap, by omega, ?_⟩
          apply hinsert m _ _ m (hllen _ _ _ (by omega) hf)
            (hllen _ _ _ (by omega) (by omega)) le_rfl
          · intro index hi
            rw [hle (m + 1) start finish index (by omega) (by omega) (by omega),
              hle m start finish index (by omega) hf hi]
          · rw [hle (m + 1) start finish m (by omega) (by omega) (by omega)]
            split_ifs <;> omega
          · intro index hi hb
            omega
        · subst finish site
          right; left
          refine ⟨start, m + 1, by omega, le_rfl, ?_⟩
          apply hinsert m _ _ start (hllen _ _ _ (by omega) le_rfl)
            (hllen _ _ _ (by omega) le_rfl) (by omega)
          · intro index hi
            rw [hle (m + 1) start (m + 1) index (by omega) le_rfl (by omega),
              hle m start m index (by omega) le_rfl (by omega)]
            split_ifs <;> omega
          · rw [hle (m + 1) start (m + 1) start (by omega) le_rfl (by omega)]
            split_ifs <;> omega
          · intro index hi hb
            rw [hle (m + 1) start (m + 1) index (by omega) le_rfl hb,
              hle m start m (index - 1) (by omega) le_rfl (by omega)]
            split_ifs <;> omega
      · obtain ⟨lower, upper, hl, hu, hf, rfl⟩ := hvalley
        have hcuts := (a_valley_forms m lower upper hl hu hf).2 site hs |>.mp hactive
        rcases hcuts with hzero | hcut
        · subst site
          by_cases hupper : upper = m
          · subst upper
            right; right; left
            refine ⟨lower, m + 1, hl, by omega, le_rfl, ?_⟩
            apply hinsert m _ _ 0 (hvlen _ _ _ hl hu le_rfl)
              (hvlen _ _ _ hl (by omega) le_rfl) (by omega)
            · intro index hi
              omega
            · rw [hve (m + 1) lower (m + 1) 0 hl (by omega) le_rfl (by omega)]
              split_ifs <;> omega
            · intro index hi hb
              rw [hve (m + 1) lower (m + 1) index hl (by omega) le_rfl hb,
                hve m lower m (index - 1) hl hu le_rfl (by omega)]
              split_ifs <;> omega
          · right; right; right
            simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
              hterminal m (by omega) _ hparent (by
                intro cut hn hc ha
                have hh := (a_valley_forms m lower upper hl hu hf).2 cut hc |>.mp ha
                have hcut : cut = m - lower + 1 := by rcases hh with hz | he <;> omega
                refine ⟨upper - lower, upper - lower + 1, by omega, by omega, ?_⟩
                rw [hve m lower upper (upper - lower) hl hu hf (by omega),
                  hve m lower upper (upper - lower + 1) hl hu hf (by omega)]
                split_ifs <;> omega)
        · subst site
          right; right; left
          refine ⟨lower, upper, hl, hu, by omega, ?_⟩
          apply hinsert m _ _ (m - lower + 1) (hvlen _ _ _ hl hu hf)
            (hvlen _ _ _ hl hu (by omega)) (by omega)
          · intro index hi
            rw [hve (m + 1) lower upper index hl hu (by omega) (by omega),
              hve m lower upper index hl hu hf (by omega)]
            split_ifs <;> omega
          · rw [hve (m + 1) lower upper (m - lower + 1) hl hu (by omega) (by omega)]
            split_ifs <;> omega
          · intro index hi hb
            rw [hve (m + 1) lower upper index hl hu (by omega) hb,
              hve m lower upper (index - 1) hl hu hf (by omega)]
            split_ifs <;> omega
      · have hzero : site = 0 := (hterm site hs).mp hactive
        subst site
        right; right; right
        simpa only [List.insertIdx_zero, Nat.add_assoc, Nat.reduceAdd] using
          hterminal m (by omega) parent hparent (by
            intro cut hn hc ha
            exact False.elim (hn ((hterm cut hc).mp ha)))
  exact hclass n hsize p hp

end D5.S3.Combinatorics.Fishburn.FishburnTenTenATree
