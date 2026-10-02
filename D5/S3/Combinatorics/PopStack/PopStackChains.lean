/- GID: D5/S3/Combinatorics/PopStack/PopStackChains
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackChains
   mirror-E: none(waiver:vertical-two-chain-characterization)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin, mathlib/module/Mathlib.Data.Finset.Max]
   utility: none
   digest: Avoiding 123, 3142 and 3412 is equivalent to two value-separated decreasing chains. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackChains

open PopStackDefs

def InD (permutation : List ℕ) : Prop :=
  ¬ Occurs [1, 2, 3] permutation ∧ ¬ Occurs [3, 1, 4, 2] permutation ∧
    ¬ Occurs [3, 4, 1, 2] permutation

theorem two_decreasing_chains (permutation : List ℕ) (hnodup : permutation.Nodup) :
    (InD permutation ↔ ∃ cut : ℕ,
      permutation.Pairwise (fun first second =>
        (first ≤ cut ↔ second ≤ cut) → second < first)) ∧
    (InD permutation → InC permutation) := by
  classical
  let value := fun position => permutation.getD position 0
  have hvalueMem : ∀ position, position < permutation.length →
      value position ∈ permutation := by
    intro position hposition
    dsimp only [value]
    rw [List.getD_eq_getElem _ _ hposition]
    exact List.getElem_mem hposition
  have hselected : ∀ positions : List ℕ, positions.Pairwise (· < ·) →
      (∀ position ∈ positions, position < permutation.length) →
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
    change value positions[index.val] = permutation[(select index).val]
    dsimp only [select, value]
    exact List.getD_eq_getElem _ _ (hbound _ (List.getElem_mem (by simpa using index.isLt)))
  have htriple : ∀ first second third, first < second → second < third →
      third < permutation.length → value first < value second → value second < value third →
      Occurs [1, 2, 3] permutation := by
    intro first second third hfirst hsecond hthird hlow hhigh
    let ranks := fun rank => if rank = 1 then value first
      else if rank = 2 then value second else value third
    refine ⟨ranks, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hlast
      change rank < 3 at hlast
      have hr : rank = 1 ∨ rank = 2 := by omega
      rcases hr with rfl | rfl <;> simp only [ranks, ↓reduceIte, Nat.reduceAdd] <;> assumption
    · intro rank hrank hlast
      change rank ≤ 3 at hlast
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hr with rfl | rfl | rfl <;> simp only [ranks, ↓reduceIte] <;>
        apply hvalueMem <;> omega
    · simpa [ranks] using hselected [first, second, third]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hposition; simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hposition; rcases hposition with rfl | rfl | rfl <;> omega)
  have hquad : ∀ first second third fourth,
      first < second → second < third → third < fourth → fourth < permutation.length →
      value second < value fourth → value fourth < value first → value first < value third →
      Occurs [3, 1, 4, 2] permutation := by
    intro first second third fourth hfirst hsecond hthird hfourth hlow hmid hhigh
    let ranks := fun rank => if rank = 1 then value second
      else if rank = 2 then value fourth else if rank = 3 then value first else value third
    refine ⟨ranks, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hlast
      change rank < 4 at hlast
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hr with rfl | rfl | rfl <;>
        simp only [ranks, ↓reduceIte, Nat.reduceAdd] <;> assumption
    · intro rank hrank hlast
      change rank ≤ 4 at hlast
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [ranks, ↓reduceIte] <;>
        apply hvalueMem <;> omega
    · simpa [ranks] using hselected [first, second, third, fourth]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hposition; simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hposition; rcases hposition with rfl | rfl | rfl | rfl <;> omega)
  have hquadSeparated : ∀ first second third fourth,
      first < second → second < third → third < fourth → fourth < permutation.length →
      value third < value fourth → value fourth < value first → value first < value second →
      Occurs [3, 4, 1, 2] permutation := by
    intro first second third fourth hfirst hsecond hthird hfourth hlow hmid hhigh
    let ranks := fun rank => if rank = 1 then value third
      else if rank = 2 then value fourth else if rank = 3 then value first else value second
    refine ⟨ranks, ?_, ?_, ?_, by simp⟩
    · intro rank hrank hlast
      change rank < 4 at hlast
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
      rcases hr with rfl | rfl | rfl <;>
        simp only [ranks, ↓reduceIte, Nat.reduceAdd] <;> assumption
    · intro rank hrank hlast
      change rank ≤ 4 at hlast
      have hr : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
      rcases hr with rfl | rfl | rfl | rfl <;> simp only [ranks, ↓reduceIte] <;>
        apply hvalueMem <;> omega
    · simpa [ranks] using hselected [first, second, third, fourth]
        (by simp [List.pairwise_cons]; omega)
        (by intro position hposition; simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hposition; rcases hposition with rfl | rfl | rfl | rfl <;> omega)
  have hcuts : InD permutation ↔ ∃ cut : ℕ,
      permutation.Pairwise (fun first second =>
        (first ≤ cut ↔ second ≤ cut) → second < first) := by
    constructor
    · rintro ⟨h123, h3142, h3412⟩
      let pairs := (((List.range permutation.length).flatMap (fun first =>
        (List.range permutation.length).map (fun second => (first, second)))).toFinset).filter
          (fun pair => pair.1 < pair.2 ∧ value pair.1 < value pair.2)
      have hpairs : ∀ first second, (first, second) ∈ pairs ↔
          first < permutation.length ∧ second < permutation.length ∧
            first < second ∧ value first < value second := by
        intro first second
        simp [pairs]
        omega
      by_cases hnonempty : pairs.Nonempty
      · let lowers := pairs.image (fun pair => value pair.1)
        have hlowers : lowers.Nonempty := hnonempty.image _
        let cut := lowers.max' hlowers
        have hcutMem : cut ∈ lowers := Finset.max'_mem _ _
        obtain ⟨⟨left, right⟩, hpair, hcut⟩ := Finset.mem_image.mp hcutMem
        change value left = cut at hcut
        obtain ⟨hleft, hright, hlr, hvalues⟩ := (hpairs left right).mp hpair
        have hcross : ∀ first second, (first, second) ∈ pairs →
            value first ≤ cut ∧ cut < value second := by
          intro first second hpair'
          obtain ⟨hfirst, hsecond, hfs, hascent⟩ := (hpairs first second).mp hpair'
          have hle : value first ≤ cut :=
            Finset.le_max' lowers _ (Finset.mem_image.mpr ⟨(first, second), hpair', rfl⟩)
          refine ⟨hle, ?_⟩
          by_contra hnot
          have hupper : value second ≤ value left := by omega
          by_cases heq : value second = value left
          · have hindex : second = left := by
              have hh : (⟨second, hsecond⟩ : Fin permutation.length) = ⟨left, hleft⟩ :=
                hnodup.injective_get (by
                  simpa only [value, List.getD_eq_getElem _ _ hsecond,
                    List.getD_eq_getElem _ _ hleft, List.get_eq_getElem] using heq)
              exact congrArg Fin.val hh
            subst second
            exact h123 (htriple first left right hfs hlr hright hascent hvalues)
          · have hstrict : value second < value left := by omega
            have hdistinct : first ≠ left ∧ second ≠ left ∧ first ≠ right ∧
                second ≠ right := by
              constructor
              · intro hequal; subst first; omega
              constructor
              · intro hequal; subst second; omega
              constructor
              · intro hequal; subst first; omega
              · intro hequal; subst second; omega
            by_cases hfl : first < left
            · exact h123 (htriple first left right hfl hlr hright (by omega) hvalues)
            · have hlf : left < first := by omega
              by_cases hfr : first < right
              · by_cases hsr : second < right
                · exact h123 (htriple first second right hfs hsr hright hascent (by omega))
                · exact h3142 (hquad left first right second hlf hfr
                    (by omega) hsecond hascent hstrict hvalues)
              · exact h3412 (hquadSeparated left right first second hlr
                  (by omega) hfs hsecond hascent hstrict hvalues)
        refine ⟨cut, List.pairwise_iff_getElem.mpr ?_⟩
        intro first second hfirst hsecond hfs hsame
        have hne : value first ≠ value second := by
          have hh := List.pairwise_iff_getElem.mp hnodup first second hfirst hsecond hfs
          simpa only [value, List.getD_eq_getElem _ _ hfirst,
            List.getD_eq_getElem _ _ hsecond] using hh
        have hsame' : value first ≤ cut ↔ value second ≤ cut := by
          simpa only [value, List.getD_eq_getElem _ _ hfirst,
            List.getD_eq_getElem _ _ hsecond] using hsame
        have hresult : value second < value first := by
          by_contra hnot
          obtain ⟨hlow, hhigh⟩ := hcross first second
            ((hpairs first second).mpr ⟨hfirst, hsecond, hfs, by omega⟩)
          have := hsame'.mp hlow
          omega
        simpa only [value, List.getD_eq_getElem _ _ hfirst,
          List.getD_eq_getElem _ _ hsecond] using hresult
      · refine ⟨0, List.pairwise_iff_getElem.mpr ?_⟩
        intro first second hfirst hsecond hfs _
        have hne := List.pairwise_iff_getElem.mp hnodup first second hfirst hsecond hfs
        by_contra hnot
        have hascent : value first < value second := by
          dsimp only [value]
          rw [List.getD_eq_getElem _ _ hfirst, List.getD_eq_getElem _ _ hsecond]
          omega
        exact hnonempty ⟨(first, second), (hpairs first second).mpr
          ⟨hfirst, hsecond, hfs, hascent⟩⟩
    · rintro ⟨cut, hchain⟩
      have hcross : ∀ first second, first < second → [first, second].Sublist permutation →
          first ≤ cut ∧ cut < second := by
        intro first second hascent hsub
        have hh := (List.pairwise_cons.mp (hchain.sublist hsub)).1 second (by simp)
        by_cases hfirst : first ≤ cut <;> by_cases hsecond : second ≤ cut
        · have := hh (by tauto); omega
        · omega
        · omega
        · have := hh (by tauto); omega
      have h123 : ¬ Occurs [1, 2, 3] permutation := by
        rintro ⟨ranks, hinc, _, hsub, _⟩
        have h12 : ranks 1 < ranks 2 := hinc 1 (by omega) (by decide)
        have h23 : ranks 2 < ranks 3 := hinc 2 (by omega) (by decide)
        have hfirst := hcross (ranks 1) (ranks 2) h12
          ((show [1, 2].Sublist [1, 2, 3] by decide).map ranks |>.trans hsub)
        have hsecond := hcross (ranks 2) (ranks 3) h23
          ((show [2, 3].Sublist [1, 2, 3] by decide).map ranks |>.trans hsub)
        omega
      have h3142 : ¬ Occurs [3, 1, 4, 2] permutation := by
        rintro ⟨ranks, hinc, _, hsub, _⟩
        have h12 : ranks 1 < ranks 2 := hinc 1 (by omega) (by decide)
        have h23 : ranks 2 < ranks 3 := hinc 2 (by omega) (by decide)
        have h34 : ranks 3 < ranks 4 := hinc 3 (by omega) (by decide)
        have hfirst := hcross (ranks 1) (ranks 2) h12
          ((show [1, 2].Sublist [3, 1, 4, 2] by decide).map ranks |>.trans hsub)
        have hsecond := hcross (ranks 3) (ranks 4) h34
          ((show [3, 4].Sublist [3, 1, 4, 2] by decide).map ranks |>.trans hsub)
        omega
      have h3412 : ¬ Occurs [3, 4, 1, 2] permutation := by
        rintro ⟨ranks, hinc, _, hsub, _⟩
        have h12 : ranks 1 < ranks 2 := hinc 1 (by omega) (by decide)
        have h23 : ranks 2 < ranks 3 := hinc 2 (by omega) (by decide)
        have h34 : ranks 3 < ranks 4 := hinc 3 (by omega) (by decide)
        have hfirst := hcross (ranks 1) (ranks 2) h12
          ((show [1, 2].Sublist [3, 4, 1, 2] by decide).map ranks |>.trans hsub)
        have hsecond := hcross (ranks 3) (ranks 4) h34
          ((show [3, 4].Sublist [3, 4, 1, 2] by decide).map ranks |>.trans hsub)
        omega
      exact ⟨h123, h3142, h3412⟩
  refine ⟨hcuts, ?_⟩
  intro hD pattern hpattern hocc
  have htable : ∀ pattern ∈ basis, ∃ small ∈ [[1, 2, 3], [3, 1, 4, 2], [3, 4, 1, 2]],
      ∃ ranks ∈ [[2, 3, 4], [2, 3, 5], [2, 3, 4, 5], [1, 3, 4, 5]],
      ranks.length = small.length ∧ ranks.Pairwise (· < ·) ∧
      (small.map (fun rank => ranks.getD (rank - 1) 0)).Sublist pattern ∧
      ∀ rank ∈ ranks, 1 ≤ rank ∧ rank ≤ pattern.length := by decide
  obtain ⟨small, hsmall, selected, _, hlength, horder, hsub, hbounds⟩ := htable pattern hpattern
  obtain ⟨ranks, hinc, hmem, hsubPattern, _⟩ := hocc
  have hmono : ∀ first second, 1 ≤ first → first < second → second ≤ pattern.length →
      ranks first < ranks second := by
    intro first second hfirst hlt hsecond
    induction second with
    | zero => omega
    | succ second ih =>
      by_cases heq : first = second
      · subst first; exact hinc second hfirst (by omega)
      · have hh := ih (by omega) (by omega)
        have hi := hinc second (by omega) (by omega)
        omega
  let compose := fun rank => ranks (selected.getD (rank - 1) 0)
  have hgetBound : ∀ rank, 1 ≤ rank → rank ≤ small.length →
      1 ≤ selected.getD (rank - 1) 0 ∧
        selected.getD (rank - 1) 0 ≤ pattern.length := by
    intro rank hfirst hlast
    apply hbounds
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem (by omega)
  have hsmallOccurs : Occurs small permutation := by
    refine ⟨compose, ?_, ?_, ?_, by simp⟩
    · intro rank hfirst hlast
      have hbefore := hgetBound rank hfirst (by omega)
      have hafter := hgetBound (rank + 1) (by omega) (by omega)
      apply hmono _ _ hbefore.1 _ hafter.2
      have hh := List.pairwise_iff_getElem.mp horder
        (rank - 1) rank (by omega) (by omega) (by omega)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by omega)]
      simpa only [Nat.add_sub_cancel] using hh
    · intro rank hfirst hlast
      obtain ⟨hpositive, hlast'⟩ := hgetBound rank hfirst hlast
      exact hmem _ hpositive hlast'
    · simpa only [List.map_map, Function.comp_def, compose] using
        (hsub.map ranks).trans hsubPattern
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsmall
  rcases hsmall with rfl | rfl | rfl
  · exact hD.1 hsmallOccurs
  · exact hD.2.1 hsmallOccurs
  · exact hD.2.2 hsmallOccurs

end D5.S3.Combinatorics.PopStack.PopStackChains
