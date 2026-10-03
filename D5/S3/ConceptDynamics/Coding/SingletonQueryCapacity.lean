/- GID: D5/S3/ConceptDynamics/Coding/SingletonQueryCapacity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/SingletonQueryCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singleton-or-constant adaptive binary queries have linear source capacity. -/

import D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity

open D5.S3.ConceptDynamics.Coding.FiberBinaryIdentification

open Classical in
/-- A globally constant question may return either Boolean value. All other
questions have at most one true source, even at unrealized histories. -/
theorem singleton_or_constant_query_capacity
    {X : Type*} [Fintype X] {depth : Nat}
    (protocol : BinaryProtocol X depth)
    (identifies : Function.Injective protocol.transcript)
    (questions : ∀ (round : Fin depth) (history : Fin round.val → Bool),
      (∃ answer : Bool, ∀ x, protocol.question round history x = answer) ∨
      (Finset.univ.filter fun x : X => protocol.question round history x = true).card ≤ 1) :
    Fintype.card X ≤ depth + 1 := by
  classical
  have survivors : ∀ t : Nat, t ≤ depth → ∃ s : Finset X,
      Fintype.card X ≤ s.card + t ∧
      ∀ x ∈ s, ∀ y ∈ s, ∀ i : Fin depth, i.val < t →
        (protocol.transcript x).getLsb i = (protocol.transcript y).getLsb i := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨Finset.univ, by simp, ?_⟩
      intro x hx y hy i hi
      omega
    | succ t ih =>
      intro ht
      obtain ⟨s, hcard, hsame⟩ := ih (by omega)
      by_cases hempty : s = ∅
      · refine ⟨s, by omega, ?_⟩
        simp [hempty]
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      let round : Fin depth := ⟨t, by omega⟩
      let history : Fin t → Bool := fun j =>
        (protocol.transcript a).getLsb ⟨j.val, j.isLt.trans round.isLt⟩
      have bit_question (x : X) (hx : x ∈ s) :
          (protocol.transcript x).getLsb round = protocol.question round history x := by
        rw [protocol.transcript_consistent]
        congr 1
        funext j
        exact hsame x hx a ha ⟨j.val, j.isLt.trans round.isLt⟩ j.isLt
      rcases questions round history with ⟨answer, hconstant⟩ | hsparse
      · refine ⟨s, by omega, ?_⟩
        intro x hx y hy i hi
        by_cases hit : i.val < t
        · exact hsame x hx y hy i hit
        · have hir : i = round := Fin.ext (by dsimp [round]; omega)
          rw [hir, bit_question x hx, bit_question y hy, hconstant x, hconstant y]
      · let kept := s.filter fun x => ¬ protocol.question round history x = true
        have hremoved : (s.filter fun x => protocol.question round history x = true).card ≤ 1 :=
          (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans hsparse
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := s) (fun x => protocol.question round history x = true)
        refine ⟨kept, by dsimp [kept]; omega, ?_⟩
        intro x hx y hy i hi
        obtain ⟨hxs, hxfalse⟩ := Finset.mem_filter.mp hx
        obtain ⟨hys, hyfalse⟩ := Finset.mem_filter.mp hy
        by_cases hit : i.val < t
        · exact hsame x hxs y hys i hit
        · have hir : i = round := Fin.ext (by dsimp [round]; omega)
          rw [hir, bit_question x hxs, bit_question y hys]
          exact (Bool.eq_false_iff.mpr hxfalse).trans (Bool.eq_false_iff.mpr hyfalse).symm
  obtain ⟨s, hcard, hsame⟩ := survivors depth le_rfl
  have hlast : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro x hx y hy
    apply identifies
    apply BitVec.eq_of_getElem_eq
    intro i hi
    exact hsame x hx y hy ⟨i, hi⟩ hi)
  omega

#print axioms singleton_or_constant_query_capacity

end D5.S3.ConceptDynamics.Coding.SingletonQueryCapacity
