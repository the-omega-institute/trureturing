/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeqOccurs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeqOccurs
   mirror-E: none(waiver:short-pattern-rank-construction)
   anchors: [mathlib/module/Mathlib.Data.List.NodupEquivFin]
   utility: none
   digest: Constructs ranked occurrences from three ordered positions and their comparisons. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs

open D5.S3.Combinatorics Nonnesting

theorem occurs_three_iff (a b c : ℕ) (w : List ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hfull : ∀ rank, 1 ≤ rank → rank ≤ max a (max b c) →
      rank = a ∨ rank = b ∨ rank = c) :
    NonnestingDefs.Occurs [a, b, c] w ↔
      ∃ first second third : ℕ,
        first < second ∧ second < third ∧ third < w.length ∧
        (a < b ↔ w.getD first 0 < w.getD second 0) ∧
        (a < c ↔ w.getD first 0 < w.getD third 0) ∧
        (b < c ↔ w.getD second 0 < w.getD third 0) ∧
        (a = b ↔ w.getD first 0 = w.getD second 0) ∧
        (a = c ↔ w.getD first 0 = w.getD third 0) ∧
        (b = c ↔ w.getD second 0 = w.getD third 0) := by
  have hletters : NonnestingDefs.letters [a, b, c] = max a (max b c) := by
    simp [NonnestingDefs.letters]
  constructor
  · rintro ⟨values, hstep, _, hsub, _⟩
    rw [hletters] at hstep
    have hmono : ∀ left right : ℕ, 1 ≤ left → left < right →
        right ≤ max a (max b c) → values left < values right := by
      intro left right
      induction right with
      | zero => omega
      | succ right ih =>
        intro hleft hlt hright
        by_cases heq : left = right
        · subst left
          exact hstep right hleft (by omega)
        · exact lt_trans (ih hleft (by omega) (by omega))
            (hstep right (by omega) (by omega))
    have hrel : ∀ left right : ℕ, 1 ≤ left → left ≤ max a (max b c) →
        1 ≤ right → right ≤ max a (max b c) →
        (left < right ↔ values left < values right) ∧
        (left = right ↔ values left = values right) := by
      intro left right hleft hleftmax hright hrightmax
      constructor
      · constructor
        · exact fun hlt => hmono left right hleft hlt hrightmax
        · intro hlt
          rcases lt_trichotomy left right with hlt' | heq | hgt
          · exact hlt'
          · subst right; omega
          · have := hmono right left hright hgt hleftmax
            omega
      · constructor
        · exact congrArg values
        · intro heq
          rcases lt_trichotomy left right with hlt | heq' | hgt
          · have := hmono left right hleft hlt hrightmax
            omega
          · exact heq'
          · have := hmono right left hright hgt hleftmax
            omega
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first : Fin w.length := positions ⟨0, by simp⟩
    let second : Fin w.length := positions ⟨1, by simp⟩
    let third : Fin w.length := positions ⟨2, by simp⟩
    have hfirst : w.getD first.val 0 = values a := by
      rw [List.getD_eq_get]
      simpa [first] using (hpositions ⟨0, by simp⟩).symm
    have hsecond : w.getD second.val 0 = values b := by
      rw [List.getD_eq_get]
      simpa [second] using (hpositions ⟨1, by simp⟩).symm
    have hthird : w.getD third.val 0 = values c := by
      rw [List.getD_eq_get]
      simpa [third] using (hpositions ⟨2, by simp⟩).symm
    refine ⟨first, second, third, ?_, ?_, third.is_lt, ?_⟩
    · exact positions.strictMono (by change (0 : ℕ) < 1; omega)
    · exact positions.strictMono (by change (1 : ℕ) < 2; omega)
    rw [hfirst, hsecond, hthird]
    have hab := hrel a b ha (by omega) hb (by omega)
    have hac := hrel a c ha (by omega) hc (by omega)
    have hbc := hrel b c hb (by omega) hc (by omega)
    exact ⟨hab.1, hac.1, hbc.1, hab.2, hac.2, hbc.2⟩
  · rintro ⟨first, second, third, hfs, hst, hthird,
      hablt, haclt, hbclt, habeq, haceq, hbceq⟩
    let values : ℕ → ℕ := fun rank =>
      if rank = a then w.getD first 0
      else if rank = b then w.getD second 0 else w.getD third 0
    have hfirst : values a = w.getD first 0 := by simp [values]
    have hsecond : values b = w.getD second 0 := by
      dsimp [values]
      split_ifs with heq
      · exact (habeq.mp heq.symm)
      · rfl
      · contradiction
    have hthirdval : values c = w.getD third 0 := by
      dsimp [values]
      split_ifs with heq heq
      · exact haceq.mp heq.symm
      · exact hbceq.mp heq.symm
      · rfl
    refine ⟨values, ?_, ?_, ?_, by simp⟩
    · rw [hletters]
      intro rank hrank hmax
      rcases hfull rank hrank (by omega) with heq | heq | heq <;>
        rcases hfull (rank + 1) (by omega) (by omega) with hnext | hnext | hnext <;>
        rw [hnext, heq] <;> simp only [hfirst, hsecond, hthirdval] <;> omega
    · rw [hletters]
      intro rank hrank hmax
      rcases hfull rank hrank hmax with rfl | rfl | rfl
      · rw [hfirst, List.getD_eq_getElem w 0 (by omega)]
        exact List.getElem_mem _
      · rw [hsecond, List.getD_eq_getElem w 0 (by omega)]
        exact List.getElem_mem _
      · rw [hthirdval, List.getD_eq_getElem w 0 hthird]
        exact List.getElem_mem _
    · apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
      let select : Fin ([a, b, c].map values).length → Fin w.length := fun index =>
        if index.val = 0 then ⟨first, by omega⟩
        else if index.val = 1 then ⟨second, by omega⟩ else ⟨third, hthird⟩
      have hselect : StrictMono select := by
        intro left right hlt
        change left.val < right.val at hlt
        have hl := left.is_lt
        have hr := right.is_lt
        simp only [List.length_map, List.length_cons, List.length_nil] at hl hr
        dsimp [select]
        split_ifs <;> simp only [Fin.mk_lt_mk] <;> omega
      refine ⟨OrderEmbedding.ofStrictMono select hselect, ?_⟩
      intro index
      have hi := index.is_lt
      simp only [List.length_map, List.length_cons, List.length_nil] at hi
      have hcases : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 := by omega
      rcases hcases with hzero | hone | htwo
      · have heq : index = ⟨0, by simp⟩ := Fin.ext hzero
        subst index
        rw [List.getD_eq_getElem w 0 (by omega : first < w.length)] at hfirst
        simpa [select] using hfirst
      · have heq : index = ⟨1, by simp⟩ := Fin.ext hone
        subst index
        rw [List.getD_eq_getElem w 0 (by omega : second < w.length)] at hsecond
        simpa [select] using hsecond
      · have heq : index = ⟨2, by simp⟩ := Fin.ext htwo
        subst index
        rw [List.getD_eq_getElem w 0 hthird] at hthirdval
        simpa [select] using hthirdval

end D5.S3.Combinatorics.InversionSeq.InversionSeqOccurs
