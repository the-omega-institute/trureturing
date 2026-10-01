/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateInsertion
   mirror-E: none(waiver:first-endpoint-insertion-scan)
   anchors: []
   utility: none
   digest: The three-letter insertion preserves the word and successor avoidance tests. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateUFamilies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords

def I (parameter : List ℕ) : List ℕ :=
  [parameter.length + 3, parameter.length + 2] ++
    (parameter.drop 1).map (· + 1) ++ [1, parameter.length + 1]

set_option maxHeartbeats 1200000 in
theorem insertion_scan (parameter : List ℕ)
    (hperm : parameter.Perm (List.range' 1 parameter.length))
    (hsize : 2 ≤ parameter.length) (hfirst : parameter.getD 0 0 = parameter.length) :
    (I parameter).Perm (List.range' 1 (parameter.length + 3)) ∧
      b (I parameter) =
        [parameter.length + 2] ++ ((b parameter).take (parameter.length - 1)).map (· + 1) ++
          [1, (b parameter).getD (parameter.length - 1) 0 + 1, parameter.length + 3] ∧
      (¬ Contains [1, 3, 2] [] 3 (I parameter) ↔
        ¬ Contains [1, 3, 2] [] 3 parameter) ∧
      (¬ Contains [1, 3, 2] [] 3 (b (I parameter)) ↔
        ¬ Contains [1, 3, 2] [] 3 (b parameter)) ∧
      ∀ inserted : List ℕ,
        inserted.Perm (List.range' 1 (parameter.length + 3)) →
        inserted.getD 0 0 = parameter.length + 3 →
        inserted.getD 1 0 = parameter.length + 2 →
        inserted.getD (parameter.length + 1) 0 = 1 →
        inserted.getD (parameter.length + 2) 0 = parameter.length + 1 →
        ∃! seed : List ℕ, seed.Perm (List.range' 1 parameter.length) ∧
          seed.getD 0 0 = parameter.length ∧ I seed = inserted := by
  have contains132_iff_indices (p : List ℕ) :
      Contains [1, 3, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] < p[k.val] ∧
          p[k.val] < p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [h0, h2] using hlt 1 (by omega) (by omega)
      · simpa only [h2, h1] using hlt 2 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[i.val] else if t = 2 then p[k.val]
        else p[j.val]
      have hx1 : x 1 = p[i.val] := by simp [x]
      have hx2 : x 2 = p[k.val] := by simp [x]
      have hx3 : x 3 = p[j.val] := by simp [x]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
        intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 := by omega
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hkj]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub

  let size := parameter.length
  let word := I parameter
  have hlength : word.length = size + 3 := by simp [word, I, size]; omega
  have hnodup : parameter.Nodup := hperm.nodup_iff.mpr List.nodup_range'
  have hsplit : parameter = size :: parameter.drop 1 := by
    cases parameter with
    | nil => simp at hsize
    | cons maximum tail => simpa [size] using hfirst
  have hrange : (List.range' 1 size).Perm (size :: List.range' 1 (size - 1)) := by
    have heq : List.range' 1 size = List.range' 1 (size - 1) ++ [size] := by
      have hconcat := List.range'_1_concat (s := 1) (n := size - 1)
      simpa only [show size - 1 + 1 = size by omega,
        show 1 + (size - 1) = size by omega] using hconcat
    rw [heq]
    simpa using (List.perm_middle (l₁ := List.range' 1 (size - 1))
      (l₂ := []) (a := size))
  have htail : (parameter.drop 1).Perm (List.range' 1 (size - 1)) := by
    have heq := hperm.trans hrange
    rw [hsplit] at heq
    exact heq.cons_inv
  have hmiddle (value : ℕ) :
      value ∈ (parameter.drop 1).map (· + 1) ↔ 2 ≤ value ∧ value ≤ size := by
    constructor
    · intro hmem
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (htail.mem_iff.mp hold)
      omega
    · intro hbound
      refine List.mem_map.mpr ⟨value - 1, ?_, by omega⟩
      exact htail.mem_iff.mpr (List.mem_range'.mpr
        ⟨value - 2, by omega, by omega⟩)
  have hwordnodup : word.Nodup := by
    have hmiddlend : ((parameter.drop 1).map (· + 1)).Nodup :=
      List.Nodup.map (f := fun value : ℕ => value + 1)
        (by intro left right heq; dsimp at heq; omega) (hnodup.drop (i := 1))
    have hsuffix : ((parameter.drop 1).map (· + 1) ++ [1, size + 1]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hmiddlend, by simp; omega, ?_⟩
      intro left hleft right hright
      have hbound := (hmiddle left).mp hleft
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hright
      rcases hright with rfl | rfl <;> omega
    change ((size + 3) :: (size + 2) ::
      ((parameter.drop 1).map (· + 1) ++ [1, size + 1])).Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro hmem
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
      rcases hmem with heq | hmid | heq | heq
      · omega
      · have := (hmiddle (size + 3)).mp hmid; omega
      · omega
      · omega
    · apply List.nodup_cons.mpr
      refine ⟨?_, hsuffix⟩
      intro hmem
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with hmid | heq | heq
      · have := (hmiddle (size + 2)).mp hmid; omega
      · omega
      · omega
  have hwordmem (value : ℕ) : value ∈ word ↔ 1 ≤ value ∧ value ≤ size + 3 := by
    change value ∈ [size + 3, size + 2] ++
      (parameter.drop 1).map (· + 1) ++ [1, size + 1] ↔ _
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hmiddle]
    omega
  have hwordperm : word.Perm (List.range' 1 (size + 3)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hwordnodup List.nodup_range'
    ext value
    simp only [List.mem_toFinset, hwordmem, List.mem_range']
    constructor
    · intro hbound; exact ⟨value - 1, by omega, by omega⟩
    · rintro ⟨offset, hoffset, heq⟩; omega
  have hget (index : ℕ) (hindex : index < size + 3) : word.getD index 0 =
      if index = 0 then size + 3 else if index = 1 then size + 2
      else if index < size + 1 then parameter.getD (index - 1) 0 + 1
      else if index = size + 1 then 1 else size + 1 := by
    cases index with
    | zero => simp [word, I, size]
    | succ index =>
      cases index with
      | zero => simp [word, I, size]
      | succ index =>
        simp only [word, I, List.cons_append, List.nil_append,
          List.getD_cons_succ, show index + 1 + 1 ≠ 0 by omega,
          show index + 1 + 1 ≠ 1 by omega, if_false]
        by_cases hmiddleindex : index < size - 1
        · rw [List.getD_append _ _ 0 _ (by simp; omega),
            List.getD_eq_getElem _ 0 (by simp; omega), List.getElem_map,
            List.getElem_drop, if_pos (by omega)]
          rw [List.getD_eq_getElem _ 0 (by omega)]
          congr 2
          omega
        · rw [List.getD_append_right _ _ 0 _ (by simp; omega)]
          simp only [List.length_map, List.length_drop]
          rw [if_neg (by omega : ¬ index + 1 + 1 < size + 1)]
          by_cases heq : index + 2 = size + 1
          · rw [if_pos (by omega), show index - (parameter.length - 1) = 0 by omega]
            rfl
          · rw [if_neg (by omega), show index - (parameter.length - 1) = 1 by omega]
            rfl
  have hwordindex (index : ℕ) (hindex : index < size + 3) :
      word.idxOf (word.getD index 0) = index := by
    rw [List.getD_eq_getElem _ 0 (by omega)]
    simpa using List.get_idxOf hwordnodup ⟨index, by omega⟩
  have hparamindex (value : ℕ) (hvalue : 1 ≤ value) (hbound : value ≤ size) :
      parameter.idxOf value < size ∧ parameter.getD (parameter.idxOf value) 0 = value := by
    have hmem : value ∈ parameter := hperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨value - 1, by omega, by omega⟩)
    have hindex := List.idxOf_lt_length_of_mem hmem
    refine ⟨hindex, ?_⟩
    rw [List.getD_eq_getElem _ 0 hindex]
    exact List.getElem_idxOf hindex
  have hbget (index : ℕ) (hindex : index < size) : (b parameter).getD index 0 =
      if parameter.idxOf (index + 1) + 1 < size then
        parameter.getD (parameter.idxOf (index + 1) + 1) 0 + 1 else 1 := by
    rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
    simp only [b, List.getElem_map, List.getElem_range'_1]
    rw [Nat.add_comm 1 index]
  have hbwordget (index : ℕ) (hindex : index < size + 3) :
      (b word).getD index 0 =
        if index = 0 then size + 2 else if index < size then
          (b parameter).getD (index - 1) 0 + 1 else if index = size then 1
        else if index = size + 1 then (b parameter).getD (size - 1) 0 + 1
        else size + 3 := by
    rw [List.getD_eq_getElem _ 0 (by simp [b]; omega)]
    conv_lhs => simp only [b, List.getElem_map, List.getElem_range'_1]
    by_cases hzero : index = 0
    · subst index
      have hidx := hwordindex (size + 1) (by omega)
      rw [hget _ (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos rfl] at hidx
      rw [hidx, if_pos (by omega), hget _ (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · by_cases hmid : index < size
      · have hpi := hparamindex index (by omega) (by omega)
        have hpipos : 0 < parameter.idxOf index := by
          by_contra hnot
          have heq : parameter.idxOf index = 0 := by omega
          rw [heq, hfirst] at hpi
          omega
        have hidx := hwordindex (parameter.idxOf index + 1) (by omega)
        rw [hget _ (by omega), if_neg (by omega), if_neg (by omega),
          if_pos (by omega), show parameter.idxOf index + 1 - 1 =
            parameter.idxOf index by omega, hpi.2] at hidx
        rw [Nat.add_comm 1 index, hidx, if_neg hzero, if_pos hmid,
          hbget _ (by omega), show index - 1 + 1 = index by omega]
        by_cases hnext : parameter.idxOf index + 1 < size
        · rw [if_pos (by omega), hget _ (by omega), if_neg (by omega),
            if_neg (by omega), if_pos (by omega), if_pos hnext]
          congr 2
        · rw [if_pos (by omega), hget _ (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg hnext]
      · by_cases heq : index = size
        · subst index
          have hidx := hwordindex (size + 2) (by omega)
          rw [hget _ (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)] at hidx
          rw [Nat.add_comm 1 size, hidx, if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl]
        · by_cases heqnext : index = size + 1
          · subst index
            have hidx := hwordindex 1 (by omega)
            rw [hget _ (by omega), if_neg (by omega), if_pos rfl] at hidx
            have hpidx : parameter.idxOf size = 0 := by
              have heq := List.get_idxOf hnodup ⟨0, by omega⟩
              change parameter.idxOf parameter[0] = 0 at heq
              rw [← List.getD_eq_getElem _ 0 (by omega), hfirst] at heq
              exact heq
            rw [show 1 + (size + 1) = size + 2 by omega, hidx,
              if_pos (by omega), hget _ (by omega), if_neg (by omega),
              if_neg (by omega), if_pos (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega), if_pos rfl,
              hbget _ (by omega), show size - 1 + 1 = size by omega,
              hpidx, if_pos (by omega)]
          · have hfinal : index = size + 2 := by omega
            subst index
            have hidx := hwordindex 0 (by omega)
            rw [hget _ (by omega), if_pos rfl] at hidx
            rw [show 1 + (size + 2) = size + 3 by omega, hidx,
              if_pos (by omega), hget _ (by omega), if_neg (by omega),
              if_pos rfl, if_neg (by omega), if_neg (by omega),
              if_neg (by omega), if_neg (by omega)]
  have hbword : b word = [size + 2] ++
      ((b parameter).take (size - 1)).map (· + 1) ++
        [1, (b parameter).getD (size - 1) 0 + 1, size + 3] := by
    apply List.ext_getElem
    · simp [b, hlength, size]; omega
    · intro index hleft hright
      have hib : index < size + 3 := by simpa [b, hlength] using hleft
      rw [← List.getD_eq_getElem _ 0 hleft, hbwordget _ hib,
        ← List.getD_eq_getElem _ 0 hright]
      by_cases hzero : index = 0
      · subst index; simp
      · rw [show index = (index - 1) + 1 by omega, List.singleton_append,
          List.cons_append, List.getD_cons_succ, if_neg (by omega)]
        by_cases hmid : index - 1 + 1 < size
        · rw [if_pos hmid, List.getD_append _ _ 0 _ (by simp [b]; omega)]
          have hvalue : (((b parameter).take (size - 1)).map (· + 1)).getD
              (index - 1) 0 = (b parameter).getD (index - 1) 0 + 1 := by
            rw [List.getD_eq_getElem
              (((b parameter).take (size - 1)).map (· + 1)) 0 (by simp [b]; omega),
              List.getElem_map, List.getElem_take,
              List.getD_eq_getElem (b parameter) 0 (by simp [b]; omega)]
          rw [hvalue]
          congr 2
        · rw [if_neg hmid, List.getD_append_right _ _ 0 _ (by simp [b]; omega)]
          simp only [List.length_map, List.length_take, b, List.length_map,
            List.length_range', Nat.min_eq_left (by omega : size - 1 ≤ parameter.length)]
          by_cases heq : index - 1 + 1 = size
          · rw [if_pos heq, show index - 1 - (size - 1) = 0 by omega]; rfl
          · rw [if_neg heq]
            by_cases heqnext : index - 1 + 1 = size + 1
            · rw [if_pos heqnext, show index - 1 - (size - 1) = 1 by omega]; rfl
            · rw [if_neg heqnext, show index - 1 - (size - 1) = 2 by
                simp [b, hlength] at hleft; omega]; rfl
  have pattern (values : List ℕ) : Contains [1, 3, 2] [] 3 values ↔
      ∃ first middle last : ℕ, first < middle ∧ middle < last ∧ last < values.length ∧
        values.getD first 0 < values.getD last 0 ∧
        values.getD last 0 < values.getD middle 0 := by
    constructor
    · intro hcontains
      obtain ⟨first, middle, last, hfm, hml, hfl, hlm⟩ :=
        (contains132_iff_indices values).mp hcontains
      refine ⟨first, middle, last, hfm, hml, last.isLt, ?_, ?_⟩
      · simpa only [List.getD_eq_getElem _ 0 first.isLt,
          List.getD_eq_getElem _ 0 last.isLt] using hfl
      · simpa only [List.getD_eq_getElem _ 0 last.isLt,
          List.getD_eq_getElem _ 0 middle.isLt] using hlm
    · rintro ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩
      apply (contains132_iff_indices values).mpr
      refine ⟨⟨first, by omega⟩, ⟨middle, by omega⟩,
        ⟨last, hlast⟩, hfm, hml, ?_, ?_⟩
      · simpa only [List.getD_eq_getElem _ 0 (by omega : first < values.length),
          List.getD_eq_getElem _ 0 hlast] using hfl
      · simpa only [List.getD_eq_getElem _ 0 hlast,
          List.getD_eq_getElem _ 0 (by omega : middle < values.length)] using hlm
  have hbounds (index : ℕ) (hindex : index < size) :
      1 ≤ parameter.getD index 0 ∧ parameter.getD index 0 ≤ size := by
    have hmem : parameter.getD index 0 ∈ parameter := by
      rw [List.getD_eq_getElem _ 0 hindex]
      exact List.getElem_mem hindex
    obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (hperm.mem_iff.mp hmem)
    omega
  have havoidword : (¬ Contains [1, 3, 2] [] 3 word) ↔
      ¬ Contains [1, 3, 2] [] 3 parameter := by
    constructor
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩ :=
        (pattern parameter).mp hcontains
      have hpositive : 0 < first := by
        have hbound := hbounds last hlast
        by_contra hnot
        have heq : first = 0 := by omega
        rw [heq, hfirst] at hfl
        omega
      apply havoid
      apply (pattern word).mpr
      refine ⟨first + 1, middle + 1, last + 1, by omega, by omega, by omega, ?_, ?_⟩
      · rw [hget _ (by omega), hget _ (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega)]
        simpa only [Nat.add_sub_cancel] using Nat.add_lt_add_right hfl 1
      · rw [hget _ (by omega), hget _ (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega)]
        simpa only [Nat.add_sub_cancel] using Nat.add_lt_add_right hlm 1
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩ :=
        (pattern word).mp hcontains
      have hbfirst : 1 ≤ word.getD first 0 ∧ word.getD first 0 ≤ size + 3 := by
        apply (hwordmem _).mp
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_mem (by omega)
      have hbmiddle : 1 ≤ word.getD middle 0 ∧ word.getD middle 0 ≤ size + 3 := by
        apply (hwordmem _).mp
        rw [List.getD_eq_getElem _ 0 (by omega)]
        exact List.getElem_mem (by omega)
      have hindices : 2 ≤ first ∧ last < size + 1 := by
        have hlastbound : last < size + 3 := by omega
        rw [hget first (by omega), hget last hlastbound] at hfl
        rw [hget middle (by omega), hget last hlastbound] at hlm
        have hboundfirst := hbounds (first - 1)
        have hboundmiddle := hbounds (middle - 1)
        have hboundlast := hbounds (last - 1)
        split_ifs at hfl hlm <;> try omega
      apply havoid
      apply (pattern parameter).mpr
      refine ⟨first - 1, middle - 1, last - 1, by omega, by omega, by omega, ?_, ?_⟩
      · rw [hget _ (by omega), hget _ (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega)] at hfl
        omega
      · rw [hget _ (by omega), hget _ (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega), if_neg (by omega),
          if_neg (by omega), if_pos (by omega)] at hlm
        omega
  have hbperm := b_perm_of_first_max parameter hperm hfirst
  have hblength : (b parameter).length = size := by simp [b, size]
  have hbwordlength : (b word).length = size + 3 := by simp [b, hlength]
  have hbbounds (index : ℕ) (hindex : index < size) :
      1 ≤ (b parameter).getD index 0 ∧ (b parameter).getD index 0 ≤ size := by
    have hmem : (b parameter).getD index 0 ∈ b parameter := by
      rw [List.getD_eq_getElem _ 0 (by omega)]
      exact List.getElem_mem (by omega)
    obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp (hbperm.mem_iff.mp hmem)
    omega
  let embed := fun index : ℕ => if index < size - 1 then index + 1 else size + 1
  have hembed (index : ℕ) (hindex : index < size) :
      (b word).getD (embed index) 0 = (b parameter).getD index 0 + 1 := by
    dsimp [embed]
    by_cases hbefore : index < size - 1
    · rw [if_pos hbefore, hbwordget _ (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel]
    · rw [if_neg hbefore, hbwordget _ (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_pos rfl]
      congr 2
      omega
  have hembedmono (first last : ℕ) (hfl : first < last) (hlast : last < size) :
      embed first < embed last := by dsimp [embed]; split_ifs <;> omega
  have havoidsuccessor : (¬ Contains [1, 3, 2] [] 3 (b word)) ↔
      ¬ Contains [1, 3, 2] [] 3 (b parameter) := by
    constructor
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩ :=
        (pattern (b parameter)).mp hcontains
      have hlastsize : last < size := by omega
      apply havoid
      apply (pattern (b word)).mpr
      refine ⟨embed first, embed middle, embed last, hembedmono _ _ hfm (by omega),
        hembedmono _ _ hml hlastsize, ?_, ?_, ?_⟩
      · dsimp [embed]; split_ifs <;> omega
      · rw [hembed _ (by omega), hembed _ hlastsize]; omega
      · rw [hembed _ hlastsize, hembed _ (by omega)]; omega
    · intro havoid hcontains
      obtain ⟨first, middle, last, hfm, hml, hlast, hfl, hlm⟩ :=
        (pattern (b word)).mp hcontains
      have hlastsize : last < size + 3 := by omega
      have hindices : 1 ≤ first ∧ last ≤ size + 1 ∧
          first ≠ size ∧ middle ≠ size ∧ last ≠ size := by
        rw [hbwordget first (by omega), hbwordget last hlastsize] at hfl
        rw [hbwordget middle (by omega), hbwordget last hlastsize] at hlm
        have hbfirst := hbbounds (first - 1)
        have hbmiddle := hbbounds (middle - 1)
        have hblast := hbbounds (last - 1)
        have hbfinal := hbbounds (size - 1) (by omega)
        split_ifs at hfl hlm <;> try omega
      let unembed := fun index : ℕ => if index < size then index - 1 else size - 1
      have hundo (index : ℕ) (hpositive : 1 ≤ index) (hbound : index ≤ size + 1)
          (hskip : index ≠ size) : embed (unembed index) = index := by
        dsimp [embed, unembed]
        split_ifs <;> omega
      have hunbound (index : ℕ) : unembed index < size := by
        dsimp [unembed]; split_ifs <;> omega
      have hunmono (left right : ℕ) (hleft : 1 ≤ left) (hbound : right ≤ size + 1)
          (hskipleft : left ≠ size) (hskipright : right ≠ size) (hlt : left < right) :
          unembed left < unembed right := by dsimp [unembed]; split_ifs <;> omega
      have hgetun (index : ℕ) (hpositive : 1 ≤ index) (hbound : index ≤ size + 1)
          (hskip : index ≠ size) :
          (b word).getD index 0 = (b parameter).getD (unembed index) 0 + 1 := by
        have heq := hembed (unembed index) (hunbound index)
        rwa [hundo index hpositive hbound hskip] at heq
      rw [hgetun first hindices.1 (by omega) hindices.2.2.1,
        hgetun last (by omega) hindices.2.1 hindices.2.2.2.2] at hfl
      rw [hgetun last (by omega) hindices.2.1 hindices.2.2.2.2,
        hgetun middle (by omega) (by omega) hindices.2.2.2.1] at hlm
      apply havoid
      apply (pattern (b parameter)).mpr
      refine ⟨unembed first, unembed middle, unembed last,
        hunmono _ _ hindices.1 (by omega) hindices.2.2.1 hindices.2.2.2.1 hfm,
        hunmono _ _ (by omega) hindices.2.1 hindices.2.2.2.1 hindices.2.2.2.2 hml,
        by simpa only [hblength] using hunbound last, by omega, by omega⟩
  refine ⟨hwordperm, hbword, havoidword, havoidsuccessor, ?_⟩
  intro inserted hiperm hhead hsecond hpenult hlast
  have hilength : inserted.length = size + 3 := by
    simpa only [List.length_range'] using hiperm.length_eq
  let middle := (inserted.drop 2).take (size - 1)
  have hmiddlelength : middle.length = size - 1 := by
    simp only [middle, List.length_take, List.length_drop, hilength]
    omega
  have hsplit : inserted = [size + 3, size + 2] ++ middle ++ [1, size + 1] := by
    apply List.ext_getElem (by simp [hmiddlelength, hilength]; omega)
    intro index hi hj
    have hleft : inserted[index] = inserted.getD index 0 :=
      (List.getD_eq_getElem _ 0 hi).symm
    rw [hleft]
    cases index with
    | zero => simpa only [List.cons_append, List.nil_append, List.getElem_cons_zero]
        using hhead
    | succ index =>
      cases index with
      | zero => simpa only [List.cons_append, List.nil_append,
          List.getElem_cons_succ, List.getElem_cons_zero] using hsecond
      | succ index =>
        simp only [List.cons_append, List.nil_append, List.getElem_cons_succ]
        by_cases hmid : index < middle.length
        · rw [List.getElem_append_left hmid, List.getD_eq_getElem _ 0 hi]
          simp only [middle, List.getElem_take, List.getElem_drop]
          congr 1
          omega
        · rw [List.getElem_append_right (by omega)]
          by_cases hpen : index = size - 1
          · have heq : index - middle.length = 0 := by omega
            simp only [heq, List.getElem_cons_zero]
            have hp : index + 1 + 1 = size + 1 := by omega
            simpa only [hp] using hpenult
          · have heq : index - middle.length = 1 := by omega
            simp only [heq, List.getElem_cons_succ, List.getElem_cons_zero]
            have hp : index + 1 + 1 = size + 2 := by omega
            simpa only [hp] using hlast
  have hrangesplit : List.range' 1 (size + 3) =
      [1] ++ List.range' 2 (size - 1) ++ [size + 1, size + 2, size + 3] := by
    have hcore : List.range' 2 (size + 2) =
        List.range' 2 (size - 1) ++ List.range' (size + 1) 3 := by
      have hs : 2 + 1 * (size - 1) = size + 1 := by omega
      have hn : size - 1 + 3 = size + 2 := by omega
      rw [← hn, ← List.range'_append, hs]
    rw [show size + 3 = (size + 2) + 1 by omega, List.range'_succ, hcore]
    simp only [List.range'_succ, List.range'_zero,
      List.cons_append, List.nil_append]
  have hbase : (List.range' 1 (size + 3)).Perm
      ([size + 3, size + 2] ++ List.range' 2 (size - 1) ++ [1, size + 1]) := by
    rw [hrangesplit]
    apply List.perm_iff_count.mpr
    intro value
    simp only [List.count_append, List.count_cons, List.count_nil]
    omega
  have hmiddleperm : middle.Perm (List.range' 2 (size - 1)) := by
    have heq := hiperm.trans hbase
    rw [hsplit] at heq
    exact (List.perm_append_right_iff [1, size + 1]).mp
      ((List.perm_append_left_iff [size + 3, size + 2]).mp
        (by simpa only [List.append_assoc] using heq))
  let seed := size :: middle.map (· - 1)
  have hseedlength : seed.length = size := by
    simp only [seed, List.length_cons, List.length_map, hmiddlelength]
    omega
  have hsubrange : (List.range' 2 (size - 1)).map (· - 1) =
      List.range' 1 (size - 1) := by
    apply List.ext_getElem (by simp)
    intro index hi hj
    simp only [List.getElem_map, List.getElem_range'_1]
    omega
  have hseedperm : seed.Perm (List.range' 1 size) := by
    have htail := hmiddleperm.map (· - 1)
    rw [hsubrange] at htail
    have heq : List.range' 1 size = List.range' 1 (size - 1) ++ [size] := by
      have hc := List.range'_concat (s := 1) (n := size - 1) (step := 1)
      simpa only [show size - 1 + 1 = size by omega, Nat.one_mul,
        show 1 + (size - 1) = size by omega] using hc
    rw [heq]
    exact (htail.cons size).trans (List.perm_append_singleton _ _).symm
  have hrestore : (middle.map (· - 1)).map (· + 1) = middle := by
    rw [List.map_map]
    change middle.map (fun value => value - 1 + 1) = middle
    conv_rhs => rw [← List.map_id middle]
    apply List.map_inj_left.mpr
    intro value hvalue
    obtain ⟨offset, ho, heq⟩ := List.mem_range'.mp (hmiddleperm.mem_iff.mp hvalue)
    simp only [id_eq]
    omega
  have hiseed : I seed = inserted := by
    rw [I, hseedlength]
    simp only [seed, List.drop_succ_cons, List.drop_zero, hrestore]
    exact hsplit.symm
  refine ⟨seed, ⟨hseedperm, by simp only [seed, List.getD_cons_zero, size], hiseed⟩, ?_⟩
  intro other hother
  have holength : other.length = size := by
    simpa only [List.length_range'] using hother.1.length_eq
  have hotail : (other.drop 1).map (· + 1) = middle := by
    have hi := hother.2.2
    rw [I, holength, hsplit] at hi
    exact List.append_left_injective [1, size + 1]
      (List.append_right_injective [size + 3, size + 2]
        (by simpa only [List.append_assoc] using hi))
  have hrecover : other.drop 1 = middle.map (· - 1) := by
    have heq := congrArg (List.map (· - 1)) hotail
    simp only [List.map_map, Function.comp_def, Nat.add_sub_cancel] at heq
    change (other.drop 1).map id = _ at heq
    simpa only [List.map_id] using heq
  have hcons : other = size :: other.drop 1 := by
    have hne : 0 < other.length := by omega
    have hh := List.drop_eq_getElem_cons hne
    rw [List.drop_zero, ← List.getD_eq_getElem _ 0 hne, hother.2.1] at hh
    exact hh
  rw [hcons, hrecover]


end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateInsertion
