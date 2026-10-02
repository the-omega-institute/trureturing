/- GID: D5/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnBasicClassicalPatterns
   mirror-E: none(waiver:classical-maximum-occurrence-witnesses)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Maximum insertion detects 321, 231, and 4132 by ordered suffix witnesses. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicInsertion
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalPatterns

open D5.S3.Combinatorics Nonnesting

set_option maxHeartbeats 1200000 in
theorem maximum_classical_pattern_tests (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (site : ℕ) (hsite : site ≤ p.length) :
    (NonnestingDefs.Occurs [3, 2, 1] (p.insertIdx site (n + 1)) ↔
      NonnestingDefs.Occurs [3, 2, 1] p ∨
      ∃ first second, site ≤ first ∧ first < second ∧ second < p.length ∧
        p.getD second 0 < p.getD first 0) ∧
    (NonnestingDefs.Occurs [2, 3, 1] (p.insertIdx site (n + 1)) ↔
      NonnestingDefs.Occurs [2, 3, 1] p ∨
      ∃ first second, first < site ∧ site ≤ second ∧ second < p.length ∧
        p.getD second 0 < p.getD first 0) ∧
    (NonnestingDefs.Occurs [4, 1, 3, 2] (p.insertIdx site (n + 1)) ↔
      NonnestingDefs.Occurs [4, 1, 3, 2] p ∨
      ∃ first second third, site ≤ first ∧ first < second ∧ second < third ∧
        third < p.length ∧ p.getD first 0 < p.getD third 0 ∧
        p.getD third 0 < p.getD second 0) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hbound (value : ℕ) (hvalue : value ∈ p) : value ≤ n := by
    have hrange := hperm.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, heq⟩ := hrange
    omega
  have hentry (index : ℕ) (hindex : index < p.length) : p.getD index 0 ≤ n := by
    rw [List.getD_eq_getElem p 0 hindex]
    exact hbound _ (List.getElem_mem hindex)
  have hbefore (index : ℕ) (hindex : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega),
      List.getElem_insertIdx_of_lt hindex, List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter (index : ℕ) (hindex : site < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hindex,
      List.getD_eq_getElem p 0 (by omega)]
  have hmaxpos (index : ℕ) (hb : index < child.length)
      (hv : child.getD index 0 = n + 1) : index = site := by
    by_cases hleft : index < site
    · rw [hbefore index hleft] at hv
      have := hentry index (by omega)
      omega
    · by_cases heq : index = site
      · exact heq
      · rw [hafter index (by omega) hb] at hv
        have := hentry (index - 1) (by omega)
        omega
  have hfilter : ∀ (word : List ℕ) (gap : ℕ), gap ≤ word.length →
      (∀ value ∈ word, value ≠ n + 1) →
      (word.insertIdx gap (n + 1)).filter (· != n + 1) = word := by
    intro word gap
    induction gap generalizing word with
    | zero =>
      intro _ hword
      simp only [List.insertIdx_zero, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hvalue
      simpa using hword value hvalue
    | succ gap ih =>
      cases word with
      | nil => simp
      | cons head tail =>
        intro hgap hword
        have hhead := hword head (by simp)
        have htail : ∀ value ∈ tail, value ≠ n + 1 := by
          intro value hvalue
          exact hword value (by simp [hvalue])
        simpa [List.insertIdx_succ_cons, hhead] using
          congrArg (head :: ·) (ih tail (by simpa using hgap) htail)
  have hfiltered : child.filter (· != n + 1) = p :=
    hfilter p site hsite (fun value hv => by have := hbound value hv; omega)
  have hpositions (pattern : List ℕ) (values : ℕ → ℕ)
      (hsub : (pattern.map values).Sublist child) :
      ∃ select : Fin pattern.length → Fin child.length, StrictMono select ∧
        ∀ index, child.getD (select index).val 0 = values (pattern.get index) := by
    obtain ⟨embedding, heq⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let select : Fin pattern.length → Fin child.length := fun index =>
      embedding ⟨index.val, by simpa using index.is_lt⟩
    refine ⟨select, ?_, ?_⟩
    · intro first second hlt
      exact embedding.strictMono hlt
    · intro index
      rw [List.getD_eq_get]
      simpa [select, List.get_eq_getElem] using
        (heq ⟨index.val, by simpa using index.is_lt⟩).symm
  have hselected (positions : List ℕ) (horder : positions.Pairwise (· < ·))
      (hb : ∀ index ∈ positions, index < child.length) :
      (positions.map (fun index => child.getD index 0)).Sublist child := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => child.getD index 0)).length →
        Fin child.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hb _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp horder first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem child 0 _
  have hinherit (pattern : List ℕ) (size : ℕ) (values : ℕ → ℕ)
      (hstep : ∀ rank, 1 ≤ rank → rank < size → values rank < values (rank + 1))
      (hmem : ∀ rank, 1 ≤ rank → rank ≤ size → values rank ∈ child)
      (hsub : (pattern.map values).Sublist child)
      (hsmall : ∀ rank, 1 ≤ rank → rank ≤ size → values rank ≠ n + 1)
      (hranks : ∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ size) :
      ArrowWilfDefs.Contains pattern [] size p := by
    refine ⟨values, hstep, ?_, ?_, by simp⟩
    · intro rank hlo hhi
      exact (List.eq_or_mem_of_mem_insertIdx (hmem rank hlo hhi)).resolve_left
        (hsmall rank hlo hhi)
    · have hf := hsub.filter (· != n + 1)
      rw [hfiltered] at hf
      have hself : (pattern.map values).filter (· != n + 1) = pattern.map values := by
        apply List.filter_eq_self.mpr
        intro value hm
        obtain ⟨rank, hrank, rfl⟩ := List.mem_map.mp hm
        simpa using hsmall rank (hranks rank hrank).1 (hranks rank hrank).2
      rwa [hself] at hf
  have hforward (pattern : List ℕ) (size : ℕ)
      (hocc : ArrowWilfDefs.Contains pattern [] size p) :
      ArrowWilfDefs.Contains pattern [] size child := by
    obtain ⟨values, hstep, hmem, hsub, _⟩ := hocc
    refine ⟨values, hstep, ?_, hsub.trans (List.sublist_insertIdx p site (n + 1)),
      by simp⟩
    intro rank hlo hhi
    exact List.subset_insertIdx p site (n + 1) (hmem rank hlo hhi)
  change (ArrowWilfDefs.Contains [3, 2, 1] [] 3 child ↔ _) ∧
    (ArrowWilfDefs.Contains [2, 3, 1] [] 3 child ↔ _) ∧
    (ArrowWilfDefs.Contains [4, 1, 3, 2] [] 4 child ↔ _)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      by_cases htop : values 3 = n + 1
      · right
        obtain ⟨select, hmono, heq⟩ := hpositions [3, 2, 1] values hsub
        let maximum := select ⟨0, by simp⟩
        let first := select ⟨1, by simp⟩
        let second := select ⟨2, by simp⟩
        have hmf : maximum.val < first.val := hmono (by decide : (0 : Fin 3) < 1)
        have hfs : first.val < second.val := hmono (by decide : (1 : Fin 3) < 2)
        have hm : child.getD maximum.val 0 = values 3 := by
          simpa [maximum] using heq ⟨0, by simp⟩
        have hf : child.getD first.val 0 = values 2 := by
          simpa [first] using heq ⟨1, by simp⟩
        have hs : child.getD second.val 0 = values 1 := by
          simpa [second] using heq ⟨2, by simp⟩
        have hcut := hmaxpos maximum.val maximum.is_lt (hm.trans htop)
        have hfb := first.is_lt
        have hsb := second.is_lt
        rw [hafter first.val (by omega) hfb] at hf
        rw [hafter second.val (by omega) hsb] at hs
        exact ⟨first.val - 1, second.val - 1, by omega, by omega, by omega, by omega⟩
      · left
        have hm : values 3 ∈ p :=
          (List.eq_or_mem_of_mem_insertIdx (hmem 3 (by omega) (by omega))).resolve_left htop
        have hb := hbound (values 3) hm
        apply hinherit [3, 2, 1] 3 values hstep hmem hsub
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> omega
        · intro rank hrank
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank
          omega
    · rintro (hocc | ⟨first, second, hcut, hfs, hb, hlt⟩)
      · exact hforward [3, 2, 1] 3 hocc
      · let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD second 0
          else if rank = 2 then p.getD first 0 else n + 1
        have hsub := hselected [site, first + 1, second + 1]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl <;> omega)
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, hat,
          hafter (first + 1) (by omega) (by omega),
          hafter (second + 1) (by omega) (by omega), Nat.add_sub_cancel,
          Nat.add_sub_cancel] at hsub
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 := by omega
          have := hentry first (by omega)
          rcases hc with rfl | rfl <;>
            simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> apply hsub.subset <;> simp [values]
        · simpa [values] using hsub
  · constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      by_cases htop : values 3 = n + 1
      · right
        obtain ⟨select, hmono, heq⟩ := hpositions [2, 3, 1] values hsub
        let first := select ⟨0, by simp⟩
        let maximum := select ⟨1, by simp⟩
        let second := select ⟨2, by simp⟩
        have hfm : first.val < maximum.val := hmono (by decide : (0 : Fin 3) < 1)
        have hms : maximum.val < second.val := hmono (by decide : (1 : Fin 3) < 2)
        have hf : child.getD first.val 0 = values 2 := by
          simpa [first] using heq ⟨0, by simp⟩
        have hm : child.getD maximum.val 0 = values 3 := by
          simpa [maximum] using heq ⟨1, by simp⟩
        have hs : child.getD second.val 0 = values 1 := by
          simpa [second] using heq ⟨2, by simp⟩
        have hcut := hmaxpos maximum.val maximum.is_lt (hm.trans htop)
        have hsb := second.is_lt
        rw [hbefore first.val (by omega)] at hf
        rw [hafter second.val (by omega) hsb] at hs
        exact ⟨first.val, second.val - 1, by omega, by omega, by omega, by omega⟩
      · left
        have hm : values 3 ∈ p :=
          (List.eq_or_mem_of_mem_insertIdx (hmem 3 (by omega) (by omega))).resolve_left htop
        have hb := hbound (values 3) hm
        apply hinherit [2, 3, 1] 3 values hstep hmem hsub
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> omega
        · intro rank hrank
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank
          omega
    · rintro (hocc | ⟨first, second, hfirst, hsecond, hb, hlt⟩)
      · exact hforward [2, 3, 1] 3 hocc
      · let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD second 0
          else if rank = 2 then p.getD first 0 else n + 1
        have hsub := hselected [first, site, second + 1]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl <;> omega)
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil,
          hbefore first hfirst, hat, hafter (second + 1) (by omega) (by omega),
          Nat.add_sub_cancel] at hsub
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 := by omega
          have := hentry first (by omega)
          rcases hc with rfl | rfl <;>
            simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          rcases hc with rfl | rfl | rfl <;> apply hsub.subset <;> simp [values]
        · simpa [values] using hsub
  · constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      have h34 : values 3 < values 4 := hstep 3 (by omega) (by omega)
      by_cases htop : values 4 = n + 1
      · right
        obtain ⟨select, hmono, heq⟩ := hpositions [4, 1, 3, 2] values hsub
        let maximum := select ⟨0, by simp⟩
        let first := select ⟨1, by simp⟩
        let second := select ⟨2, by simp⟩
        let third := select ⟨3, by simp⟩
        have hmf : maximum.val < first.val := hmono (by decide : (0 : Fin 4) < 1)
        have hfs : first.val < second.val := hmono (by decide : (1 : Fin 4) < 2)
        have hst : second.val < third.val := hmono (by decide : (2 : Fin 4) < 3)
        have hm : child.getD maximum.val 0 = values 4 := by
          simpa [maximum] using heq ⟨0, by simp⟩
        have hf : child.getD first.val 0 = values 1 := by
          simpa [first] using heq ⟨1, by simp⟩
        have hs : child.getD second.val 0 = values 3 := by
          simpa [second] using heq ⟨2, by simp⟩
        have ht : child.getD third.val 0 = values 2 := by
          simpa [third] using heq ⟨3, by simp⟩
        have hcut := hmaxpos maximum.val maximum.is_lt (hm.trans htop)
        have hfb := first.is_lt
        have hsb := second.is_lt
        have htb := third.is_lt
        rw [hafter first.val (by omega) hfb] at hf
        rw [hafter second.val (by omega) hsb] at hs
        rw [hafter third.val (by omega) htb] at ht
        exact ⟨first.val - 1, second.val - 1, third.val - 1, by omega, by omega,
          by omega, by omega, by omega, by omega⟩
      · left
        have hm : values 4 ∈ p :=
          (List.eq_or_mem_of_mem_insertIdx (hmem 4 (by omega) (by omega))).resolve_left htop
        have hb := hbound (values 4) hm
        apply hinherit [4, 1, 3, 2] 4 values hstep hmem hsub
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
          rcases hc with rfl | rfl | rfl | rfl <;> omega
        · intro rank hrank
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hrank
          omega
    · rintro (hocc | ⟨first, second, third, hcut, hfs, hst, hb, hlt, hgt⟩)
      · exact hforward [4, 1, 3, 2] 4 hocc
      · let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD first 0
          else if rank = 2 then p.getD third 0
          else if rank = 3 then p.getD second 0 else n + 1
        have hsub := hselected [site, first + 1, second + 1, third + 1]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> omega)
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
          hat, hafter (first + 1) (by omega) (by omega),
          hafter (second + 1) (by omega) (by omega),
          hafter (third + 1) (by omega) (by omega), Nat.add_sub_cancel,
          Nat.add_sub_cancel, Nat.add_sub_cancel] at hsub
        refine ⟨values, ?_, ?_, ?_, by simp⟩
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
          have := hentry second (by omega)
          rcases hc with rfl | rfl | rfl <;>
            simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
        · intro rank hlo hhi
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
          rcases hc with rfl | rfl | rfl | rfl <;> apply hsub.subset <;> simp [values]
        · simpa [values] using hsub

end D5.S3.Combinatorics.Fishburn.FishburnBasicClassicalPatterns
