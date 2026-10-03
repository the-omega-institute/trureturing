/- GID: D5/S3/Combinatorics/PopStack/PopStackMaximumShape
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackMaximumShape
   mirror-E: none(waiver:maximum-second-simple-shape)
   anchors: [mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Pattern exclusions and a terminal interval characterize the maximum-second shape. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackMaximumShape

open PopStackDefs

theorem maximum_second_shape (permutation : List ℕ)
    (hperm : permutation.Perm (List.range' 1 permutation.length))
    (hlength : 4 ≤ permutation.length) (hmaximum : permutation.getD 1 0 = permutation.length)
    :
    let shape :=
    (∀ first second, 2 ≤ first → first < second → second < permutation.length →
      permutation.getD 0 0 < permutation.getD first 0 →
      permutation.getD 0 0 < permutation.getD second 0 →
      permutation.getD second 0 < permutation.getD first 0) ∧
    (∀ first smaller larger, 2 ≤ first → first < smaller → first < larger →
      smaller < permutation.length → larger < permutation.length →
      permutation.getD first 0 < permutation.getD 0 0 →
      permutation.getD smaller 0 < permutation.getD 0 0 →
      permutation.getD larger 0 < permutation.getD 0 0 →
      ¬ (permutation.getD smaller 0 < permutation.getD first 0 ∧
        permutation.getD first 0 < permutation.getD larger 0))
    (shape → InC permutation) ∧ (InC permutation → IsSimple permutation → shape) := by
  classical
  dsimp only
  constructor
  · rintro ⟨hupper, hlower⟩
    classical
    let value := fun index => permutation.getD index 0
    let alpha := value 0
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hbound : ∀ index, index < permutation.length → value index ≤ permutation.length := by
      intro index hindex
      have hmem : value index ∈ permutation := by
        rw [show value index = permutation[index] from List.getD_eq_getElem _ 0 hindex]
        exact List.getElem_mem hindex
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
      omega
    have hdistinct : ∀ index, 0 < index → index < permutation.length →
        value index ≠ alpha := by
      intro index hpositive hindex heq
      have hh := (List.getD_inj hindex (show 0 < permutation.length by omega) hnodup).mp heq
      omega
    have hascent : ∀ first second, first < second → second < permutation.length →
        value first < value second → value first ≤ alpha := by
      intro first second horder hsecond hvalues
      by_cases hzero : first = 0
      · subst first; exact le_rfl
      by_cases hone : first = 1
      · subst first
        have hh := hbound second hsecond
        change permutation.getD 1 0 < value second at hvalues
        omega
      by_contra hnot
      have hh := hupper first second (by omega) horder hsecond
        (show alpha < value first by omega) (show alpha < value second by omega)
      change value second < value first at hh
      omega
    have hascentStrict : ∀ first second, 0 < first → first < second →
        second < permutation.length → value first < value second → value first < alpha := by
      intro first second hpositive horder hsecond hvalues
      have hh := hascent first second horder hsecond hvalues
      have hn := hdistinct first hpositive (by omega)
      omega
    have htail : ∀ index, index < permutation.length → value index < alpha → 2 ≤ index := by
      intro index hindex hlow
      have ha := hbound 0 (by omega)
      by_cases hzero : index = 0
      · subst index; change alpha < alpha at hlow; omega
      by_cases hone : index = 1
      · subst index
        change permutation.getD 1 0 < alpha at hlow
        omega
      omega
    intro pattern hpattern hoccurs
    have hsize : 4 ≤ pattern.length := by
      simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    obtain ⟨witness, hincreasing, _, hsublist, _⟩ := hoccurs
    obtain ⟨embedding, hembedding⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsublist
    let position := fun index : ℕ => if hindex : index < pattern.length then
      (embedding ⟨index, by simpa only [List.length_map] using hindex⟩).val else 0
    have hpositionBound : ∀ index, index < pattern.length →
        position index < permutation.length := by
        intro index hindex
        dsimp only [position]
        rw [dif_pos hindex]
        exact (embedding _).isLt
    have hpositionOrder : ∀ first second, first < second → second < pattern.length →
        position first < position second := by
      intro first second horder hsecond
      dsimp only [position]
      rw [dif_pos (show first < pattern.length by omega), dif_pos hsecond]
      exact embedding.strictMono (show (⟨first, by simp; omega⟩ :
        Fin (pattern.map witness).length) < ⟨second, by simp; omega⟩ from horder)
    have hchosen : ∀ index, index < pattern.length →
        value (position index) = witness (pattern.getD index 0) := by
      intro index hindex
      have hh := hembedding ⟨index, by simpa only [List.length_map] using hindex⟩
      simp only [List.get_eq_getElem, List.getElem_map] at hh
      dsimp only [position, value]
      rw [dif_pos hindex, List.getD_eq_getElem _ 0 (embedding _).isLt,
        List.getD_eq_getElem _ 0 hindex]
      exact hh.symm
    have hp0 := hpositionBound 0 (by omega)
    have hp1 := hpositionBound 1 (by omega)
    have hp2 := hpositionBound 2 (by omega)
    have hp3 := hpositionBound 3 (by omega)
    have ho01 := hpositionOrder 0 1 (by omega) (by omega)
    have ho12 := hpositionOrder 1 2 (by omega) (by omega)
    have ho23 := hpositionOrder 2 3 (by omega) (by omega)
    have hc0 := hchosen 0 (by omega)
    have hc1 := hchosen 1 (by omega)
    have hc2 := hchosen 2 (by omega)
    have hc3 := hchosen 3 (by omega)
    have hr12 := hincreasing 1 (by omega) (by omega)
    have hr23 := hincreasing 2 (by omega) (by omega)
    have hr34 := hincreasing 3 (by omega) (by omega)
    norm_num only at hr12 hr23 hr34
    have hreject : ∀ first smaller larger, first < smaller → first < larger →
        smaller < permutation.length → larger < permutation.length →
        value first < alpha → value smaller < alpha → value larger < alpha →
        value smaller < value first → value first < value larger → False := by
      intro first smaller larger hos hol hs hl hf hsmall hlarge hsf hfl
      exact hlower first smaller larger (htail first (by omega) hf) hos hol hs hl
        hf hsmall hlarge ⟨hsf, hfl⟩
    simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1 hc2 hc3
    · have hlow := hascentStrict (position 1) (position 2) (by omega) ho12 hp2 (by omega)
      exact hreject (position 0) (position 3) (position 1) (by omega) ho01 hp3 hp1
        (by omega) (by omega) hlow (by omega) (by omega)
    all_goals have hp4 := hpositionBound 4 (by simp)
    all_goals have ho34 := hpositionOrder 3 4 (by omega) (by simp)
    all_goals have hc4 := hchosen 4 (by simp)
    all_goals simp only [List.getD_cons_zero, List.getD_cons_succ] at hc4
    all_goals have hr45 := hincreasing 4 (by omega) (by simp)
    all_goals norm_num only at hr45
    · have hlow := hascentStrict (position 2) (position 4) (by omega) (by omega) hp4
        (by omega)
      exact hreject (position 0) (position 3) (position 2) (by omega) (by omega) hp3 hp2
        (by omega) (by omega) hlow (by omega) (by omega)
    · have hlow := hascent (position 0) (position 2) (by omega) hp2 (by omega)
      exact hreject (position 1) (position 3) (position 4) (by omega) (by omega) hp3 hp4
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hlow := hascent (position 0) (position 2) (by omega) hp2 (by omega)
      exact hreject (position 1) (position 4) (position 3) (by omega) (by omega) hp4 hp3
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hlow := hascent (position 0) (position 1) ho01 hp1 (by omega)
      exact hreject (position 2) (position 3) (position 4) ho23 (by omega) hp3 hp4
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hlow := hascent (position 0) (position 1) ho01 hp1 (by omega)
      exact hreject (position 2) (position 4) (position 3) (by omega) ho23 hp4 hp3
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hlow := hascentStrict (position 2) (position 4) (by omega) (by omega) hp4
        (by omega)
      exact hreject (position 1) (position 3) (position 2) (by omega) ho12 hp3 hp2
        (by omega) (by omega) hlow (by omega) (by omega)
    all_goals have hp5 := hpositionBound 5 (by simp)
    all_goals have ho45 := hpositionOrder 4 5 (by omega) (by simp)
    all_goals have hc5 := hchosen 5 (by simp)
    all_goals simp only [List.getD_cons_zero, List.getD_cons_succ] at hc5
    all_goals have hr56 := hincreasing 5 (by omega) (by simp)
    all_goals norm_num only at hr56
    · have hlow := hascentStrict (position 1) (position 5) (by omega) (by omega) hp5
        (by omega)
      exact hreject (position 2) (position 3) (position 4) ho23 (by omega) hp3 hp4
        (by omega) (by omega) (by omega) (by omega) (by omega)
    · have hlow := hascentStrict (position 1) (position 4) (by omega) (by omega) hp4
        (by omega)
      exact hreject (position 2) (position 3) (position 5) ho23 (by omega) hp3 hp5
        (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro hC hsimple
    classical
    let value := fun index => permutation.getD index 0
    let alpha := value 0
    let maximum := permutation.length
    have hnodup := hperm.nodup_iff.mpr (List.nodup_range' 1)
    have hbounds : ∀ index, index < maximum →
        1 ≤ value index ∧ value index ≤ maximum := by
      intro index hindex
      have hmem : value index ∈ permutation := by
        rw [show value index = permutation[index] from List.getD_eq_getElem _ 0 hindex]
        exact List.getElem_mem hindex
      have hh := List.mem_range'_1.mp (hperm.mem_iff.mp hmem)
      omega
    have hinjective : ∀ first second, first < maximum → second < maximum →
        value first = value second → first = second := by
      intro first second hfirst hsecond heq
      exact (List.getD_inj hfirst hsecond hnodup).mp heq
    have hmaximumValue : value 1 = maximum := hmaximum
    have halphaBounds := hbounds 0 (by omega)
    have halphaNotMaximum : alpha ≠ maximum := by
      intro heq
      have hh := hinjective 0 1 (by omega) (by omega) (heq.trans hmaximumValue.symm)
      omega
    have halphaPositive : 1 < alpha := by
      by_contra hnot
      have halphaOne : alpha = 1 := by omega
      have hhead : alpha :: permutation.drop 1 = permutation := by
        have hh := List.drop_eq_getElem?_toList_append (l := permutation) (i := 0)
        rw [List.getElem?_eq_getElem (by omega),
          ← List.getD_eq_getElem permutation 0 (by omega)] at hh
        simpa only [List.drop_zero, Option.toList_some, List.singleton_append] using hh.symm
      have htailPerm : (permutation.drop 1).Perm (List.range' 2 (maximum - 1)) := by
        have hh : (alpha :: permutation.drop 1).Perm (List.range' 1 maximum) := by
          rw [hhead]; exact hperm
        rw [halphaOne, show maximum = (maximum - 1) + 1 by omega, List.range'_succ] at hh
        exact hh.cons_inv
      apply hsimple 1 (maximum - 1) 2 (by omega) (by omega) (by omega)
      rw [List.take_of_length_le (by simp only [List.length_drop]; omega)]
      exact htailPerm
    have hlocate : ∀ rank, 1 ≤ rank → rank ≤ maximum →
        ∃ index, index < maximum ∧ value index = rank := by
      intro rank hpositive hbound
      have hmem := hperm.mem_iff.mpr (List.mem_range'_1.mpr ⟨hpositive, by omega⟩)
      obtain ⟨index, hindex, hentry⟩ := List.mem_iff_getElem.mp hmem
      exact ⟨index, hindex, (List.getD_eq_getElem _ 0 hindex).trans hentry⟩
    have htailIndex : ∀ index, index < maximum → value index < alpha → 2 ≤ index := by
      intro index hindex hlower
      by_cases hzero : index = 0
      · subst index; change alpha < alpha at hlower; omega
      by_cases hone : index = 1
      · subst index; omega
      omega
    have hselected : ∀ positions : List ℕ, positions.Pairwise (· < ·) →
        (∀ position ∈ positions, position < maximum) →
        (positions.map value).Sublist permutation := by
      intro positions horder hbound
      apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      let select : Fin (positions.map value).length → Fin permutation.length := fun index =>
        ⟨positions[index.val]'(by simpa using index.isLt),
          hbound _ (List.getElem_mem (by simpa using index.isLt))⟩
      have hmono : StrictMono select := by
        intro first second hlt
        exact List.pairwise_iff_getElem.mp horder first.val second.val
          (by simpa using first.isLt) (by simpa using second.isLt) hlt
      refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
      intro index
      simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
      change permutation.getD (select index).val 0 = permutation[(select index).val]
      exact List.getD_eq_getElem _ 0 (select index).isLt
    have htemplates : ∀ pattern ∈ basis, pattern.Perm (List.range' 1 pattern.length) := by
      intro pattern hpattern
      simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have forbid : ∀ pattern ∈ basis, ∀ positions ranks : List ℕ,
        positions.Pairwise (· < ·) → (∀ position ∈ positions, position < maximum) →
        ranks.Pairwise (· < ·) → ranks.length = pattern.length →
        pattern.map (fun rank => ranks.getD (rank - 1) 0) = positions.map value → False := by
      intro pattern hpattern positions ranks hpositions hpositionBounds hranks hsize hmatch
      let witness := fun rank => ranks.getD (rank - 1) 0
      have hsub := hselected positions hpositions hpositionBounds
      apply hC pattern hpattern
      refine ⟨witness, ?_, ?_, ?_, by simp⟩
      · intro rank hrank hlast
        dsimp only [witness]
        rw [Nat.add_sub_cancel, List.getD_eq_getElem _ 0 (show rank - 1 < ranks.length by omega),
          List.getD_eq_getElem _ 0 (show rank < ranks.length by omega)]
        exact List.pairwise_iff_getElem.mp hranks (rank - 1) rank (by omega) (by omega)
          (by omega)
      · intro rank hrank hlast
        have hmem : rank ∈ pattern := (htemplates pattern hpattern).mem_iff.mpr
          (List.mem_range'_1.mpr ⟨hrank, by omega⟩)
        apply hsub.subset
        rw [← hmatch]
        exact List.mem_map.mpr ⟨rank, hmem, rfl⟩
      · rw [show pattern.map witness = positions.map value from hmatch]
        exact hsub
    constructor
    · intro first second hfirst horder hsecond hfirstUpper hsecondUpper
      change alpha < value first at hfirstUpper
      change alpha < value second at hsecondUpper
      change value second < value first
      by_contra hnot
      have hdistinct : value first ≠ value second := by
        intro heq
        have hh := hinjective first second (by omega) hsecond heq
        omega
      have hascent : value first < value second := by omega
      have hfirstBelowMaximum : value first < maximum := by
        have hh := hbounds second hsecond
        omega
      have hsecondBelowMaximum : value second < maximum := by
        have hh := hbounds second hsecond
        have hn : value second ≠ maximum := by
          intro heq
          have hi := hinjective second 1 hsecond (by omega) (heq.trans hmaximumValue.symm)
          omega
        omega
      have hlowerBefore : ∀ index, index < maximum → value index < alpha → index < first := by
        intro index hindex hlower
        have hindexTail := htailIndex index hindex hlower
        have hindexNeFirst : index ≠ first := by intro heq; subst index; omega
        have hindexNeSecond : index ≠ second := by intro heq; subst index; omega
        by_contra hnotBefore
        by_cases hafter : second < index
        · exact forbid [2, 3, 4, 1] (by simp [basis])
            [0, first, second, index] [value index, alpha, value first, value second]
            (by simp [List.pairwise_cons]; omega)
            (by intro position hp; simp at hp; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [alpha])
        · exact forbid [2, 5, 3, 1, 4] (by simp [basis])
            [0, 1, first, index, second] [value index, alpha, value first, value second, maximum]
            (by simp [List.pairwise_cons]; omega)
            (by intro position hp; simp at hp; omega)
            (by simp [List.pairwise_cons]; omega) rfl (by simp [alpha, hmaximumValue])
      let lowerPositions := (Finset.range maximum).filter (fun index => value index < alpha)
      have hnonempty : lowerPositions.Nonempty := by
        obtain ⟨index, hindex, hvalue⟩ := hlocate 1 (by omega) (by omega)
        exact ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hindex, by omega⟩⟩
      let lastLower := lowerPositions.max' hnonempty
      have hlastMem : lastLower ∈ lowerPositions := Finset.max'_mem _ hnonempty
      have hlastBound : lastLower < maximum := Finset.mem_range.mp (Finset.mem_filter.mp
        hlastMem).1
      have hlastLower : value lastLower < alpha := (Finset.mem_filter.mp hlastMem).2
      have hlastTail : 2 ≤ lastLower := htailIndex lastLower hlastBound hlastLower
      have hlastBefore : lastLower < first := hlowerBefore lastLower hlastBound hlastLower
      have hafterUpper : ∀ index, lastLower < index → index < maximum → alpha < value index :=
        by
          intro index hafter hindex
          have hne : value index ≠ alpha := by
            intro heq
            have hh := hinjective index 0 hindex (by omega) heq
            omega
          by_contra hnotUpper
          have hmem : index ∈ lowerPositions := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hindex, by omega⟩
          have hh : index ≤ lastLower := Finset.le_max' _ _ hmem
          omega
      have hseparated : ∀ earlier later, 2 ≤ earlier → earlier ≤ lastLower →
          alpha < value earlier → lastLower < later → later < maximum →
          value later < value earlier := by
        intro earlier later hearlier hbefore hupper hlater hlaterBound
        have hlaterUpper := hafterUpper later hlater hlaterBound
        have hearlierBound : earlier < maximum := by omega
        have hearlierBelow : value earlier < maximum := by
          have hh := hbounds earlier hearlierBound
          have hn : value earlier ≠ maximum := by
            intro heq
            have hi := hinjective earlier 1 hearlierBound (by omega)
              (heq.trans hmaximumValue.symm)
            omega
          omega
        have hlaterBelow : value later < maximum := by
          have hh := hbounds later hlaterBound
          have hn : value later ≠ maximum := by
            intro heq
            have hi := hinjective later 1 hlaterBound (by omega) (heq.trans hmaximumValue.symm)
            omega
          omega
        have hearlierNeLast : earlier ≠ lastLower := by intro heq; subst earlier; omega
        have hne : value earlier ≠ value later := by
          intro heq
          have hh := hinjective earlier later hearlierBound hlaterBound heq
          omega
        by_contra hnot
        exact forbid [2, 5, 3, 1, 4] (by simp [basis])
          [0, 1, earlier, lastLower, later]
          [value lastLower, alpha, value earlier, value later, maximum]
          (by simp [List.pairwise_cons]; omega)
          (by intro position hp; simp at hp; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [alpha, hmaximumValue])
      let suffix := permutation.drop (lastLower + 1)
      have hsuffixLength : suffix.length = maximum - (lastLower + 1) := List.length_drop
      have hsuffixNodup : suffix.Nodup := hnodup.drop
      have hsuffixMem : ∀ rank, rank ∈ suffix ↔
          ∃ index, lastLower < index ∧ index < maximum ∧ value index = rank := by
        intro rank
        constructor
        · intro hmem
          obtain ⟨offset, hoffset, hentry⟩ := List.mem_iff_getElem.mp hmem
          have hindex : lastLower + 1 + offset < maximum := by omega
          refine ⟨lastLower + 1 + offset, by omega, hindex, ?_⟩
          have hh : value (lastLower + 1 + offset) =
              suffix[offset]'hoffset := by
            simp only [suffix, List.getElem_drop]
            exact List.getD_eq_getElem _ 0 hindex
          exact hh.trans hentry
        · rintro ⟨index, hafter, hindex, hvalue⟩
          have hoffset : index - (lastLower + 1) < suffix.length := by omega
          have hh := List.getElem_mem hoffset
          have heq : suffix[index - (lastLower + 1)]'hoffset = rank := by
            simp only [suffix, List.getElem_drop]
            have hh : lastLower + 1 + (index - (lastLower + 1)) = index := by omega
            simpa only [hh, ← List.getD_eq_getElem permutation 0 hindex] using hvalue
          exact heq ▸ hh
      have hsuffixNonempty : suffix.toFinset.Nonempty := by
        exact ⟨value first, List.mem_toFinset.mpr
          ((hsuffixMem _).mpr ⟨first, hlastBefore, by omega, rfl⟩)⟩
      let top := suffix.toFinset.max' hsuffixNonempty
      have htopMem : top ∈ suffix := List.mem_toFinset.mp (Finset.max'_mem _ hsuffixNonempty)
      obtain ⟨topIndex, htopAfter, htopBound, htopValue⟩ := (hsuffixMem top).mp htopMem
      have htopUpper : alpha < top := by
        have hh := hafterUpper topIndex htopAfter htopBound
        omega
      have htopRange : top ≤ maximum := by have hh := hbounds topIndex htopBound; omega
      have hsuffixPerm : suffix.Perm (List.range' (alpha + 1) (top - alpha)) := by
        apply (List.perm_ext_iff_of_nodup hsuffixNodup (List.nodup_range' _)).mpr
        intro rank
        constructor
        · intro hmem
          obtain ⟨index, hafter, hindex, hvalue⟩ := (hsuffixMem rank).mp hmem
          have hupper := hafterUpper index hafter hindex
          have hle : rank ≤ top := Finset.le_max' _ _ (List.mem_toFinset.mpr hmem)
          exact List.mem_range'_1.mpr ⟨by omega, by omega⟩
        · intro hmem
          obtain ⟨hpositive, hbound⟩ := List.mem_range'_1.mp hmem
          have hrankUpper : alpha < rank := by omega
          obtain ⟨index, hindex, hvalue⟩ := hlocate rank (by omega) (by omega)
          have hindexTail : 2 ≤ index := by
            by_cases hzero : index = 0
            · subst index; change alpha = rank at hvalue; omega
            by_cases hone : index = 1
            · subst index
              have hn : top < maximum := by
                have hh := hbounds topIndex htopBound
                have hne : top ≠ maximum := by
                  intro heq
                  have hi := hinjective topIndex 1 htopBound (by omega)
                    (htopValue.trans (heq.trans hmaximumValue.symm))
                  omega
                omega
              omega
            omega
          have hafter : lastLower < index := by
            by_contra hnot
            have hh := hseparated index topIndex hindexTail (by omega) (by omega)
              htopAfter htopBound
            omega
          exact (hsuffixMem rank).mpr ⟨index, hafter, hindex, hvalue⟩
      have hintervalSize : top - alpha = maximum - (lastLower + 1) := by
        have hh := hsuffixPerm.length_eq
        simp only [List.length_range', hsuffixLength] at hh
        omega
      apply hsimple (lastLower + 1) (top - alpha) (alpha + 1) (by omega) (by omega) (by omega)
      change (suffix.take (top - alpha)).Perm _
      rw [List.take_of_length_le (by omega)]
      exact hsuffixPerm
    · intro first smaller larger hfirst hsmaller hlarger hsmallerBound hlargerBound
        hfirstLower hsmallerLower hlargerLower hmiddle
      change value first < alpha at hfirstLower
      change value smaller < alpha at hsmallerLower
      change value larger < alpha at hlargerLower
      change value smaller < value first ∧ value first < value larger at hmiddle
      have hlargerBelow := hbounds larger hlargerBound
      have halphaBelow : alpha < maximum := by omega
      by_cases horder : smaller < larger
      · exact forbid [4, 5, 2, 1, 3] (by simp [basis])
          [0, 1, first, smaller, larger] [value smaller, value first, value larger, alpha, maximum]
          (by simp [List.pairwise_cons]; omega)
          (by intro position hp; simp at hp; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [alpha, hmaximumValue])
      · have hne : smaller ≠ larger := by intro heq; subst smaller; omega
        exact forbid [4, 5, 2, 3, 1] (by simp [basis])
          [0, 1, first, larger, smaller] [value smaller, value first, value larger, alpha, maximum]
          (by simp [List.pairwise_cons]; omega)
          (by intro position hp; simp at hp; omega)
          (by simp [List.pairwise_cons]; omega) rfl (by simp [alpha, hmaximumValue])

end D5.S3.Combinatorics.PopStack.PopStackMaximumShape
