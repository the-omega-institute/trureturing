/- GID: D5/S3/Combinatorics/SignedDoubleRoman/PackingBase
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/PackingBase
   mirror-E: none(waiver:mixed-packing-small-carriers)
   anchors: []
   utility: none
   digest: Initial finite-carrier cases for two-relation limited packing. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedDefs

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.PackingBase

open MixedDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induction starts without graph restrictions at orders at most three. -/
theorem small_carrier (C D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (hsmall : S.card ≤ 4) (hclique : C.CliqueFreeOn (S : Set V) 4) :
    ∃ X : Finset V, X ⊆ S ∧ MixedAdmissible C D X ∧ S.card ≤ 3 * X.card := by
  classical
  by_cases hzero : S = ∅
  · subst S
    exact ⟨∅, by simp, by simp [MixedAdmissible, TwoLimited, SimpleGraph.IsIndepSet], by simp⟩
  by_cases hfour : S.card = 4
  · have hnclique : ¬ C.IsClique (S : Set V) := by
      intro h
      exact hclique (Finset.Subset.refl _)
        ((C.isNClique_iff).2 ⟨h, hfour⟩)
    obtain ⟨a, b, hab, hnonedge⟩ := C.not_isClique_iff.mp hnclique
    have hab' : (a : V) ≠ b := fun h ↦ hab (Subtype.ext h)
    refine ⟨{(a : V), (b : V)}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact a.property
      · exact b.property
    · constructor
      · intro x hx y hy hxy
        simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact C.irrefl
        · exact hnonedge
        · exact fun h ↦ hnonedge h.symm
        · exact C.irrefl
      · intro v
        exact (Finset.card_le_card (Finset.inter_subset_right)).trans Finset.card_le_two
    · simp only [Finset.card_pair hab', hfour]
      omega
  · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hzero
    refine ⟨{a}, by simpa, ?_, ?_⟩
    · constructor
      · intro x hx y hy hxy
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
        exact hxy (hx.trans hy.symm) |>.elim
      · intro v
        have hcard := Finset.card_le_card
          (Finset.inter_subset_right : (insert v (D.neighborFinset v)) ∩ {a} ⊆ {a})
        simpa using hcard.trans (by simp : ({a} : Finset V).card ≤ 2)
    · simp only [Finset.card_singleton]
      omega

end D5.S3.Combinatorics.SignedDoubleRoman.PackingBase
