/- GID: D5/S3/ConceptDynamics/Spacetime/SignedProfileRealization
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/SignedProfileRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite signed spatial profile has a balanced native event realization at time zero. -/

import D5.S3.ConceptDynamics.Spacetime.TaggedPresentation
import D5.S3.ConceptDynamics.Spacetime.HiddenArchiveTemporalDomain
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.SignedProfileRealization

open D5.S0.History.Spacetime
open HFEncoding ArchiveCarrier CoordinateEncoding
open ComplementCharge HiddenArchiveTemporalDomain
open scoped BigOperators

noncomputable section

/-- Every finitely supported integer spatial profile is realized by a finite rich
history whose entire current region is balanced in each spatial fibre. All events
are current, have time zero and empty causality, and lie in the profile support. -/
theorem exists_signed_profile (d : Nat) (r : (Fin d → Int) →₀ Int) :
    ∃ X : Rich d,
      X.1.current = Finset.univ ∧
      (∀ e, (X.1.archive.attributes e).time = 0) ∧
      (∀ e f, ¬ X.1.archive.causal e f) ∧
      (∀ e, (X.1.archive.attributes e).position ∈ r.support) ∧
      Balanced X.1 ∧
      spatialCharge X.1 X.1.current = 0 ∧
      spatialCharge X.1 X.2.val = r := by
  classical
  let E := Σ y : r.support, Fin (r y.val).natAbs × Bool
  let code : E ↪ HF :=
    { toFun := fun e => pair ((position_code_equiv d e.1.val).val)
        (IntegerRepresentatives.eventName e.2.1.val e.2.2)
      inj' := by
        intro a b h
        have hp := pair_inj.mp h
        have hy : a.1 = b.1 := Subtype.ext
          ((position_code_equiv d).injective (Subtype.ext hp.1))
        cases a with
        | mk ya ea =>
          cases b with
          | mk yb eb =>
            dsimp at hy
            cases hy
            congr 1
            exact IntegerRepresentatives.eventPair_injective hp.2 }
  let attr : E → Attributes d := fun e =>
    ⟨0, e.1.val, e.2.2, FreeMagma.of 0⟩
  let rel : E → E → Prop := fun _ _ => False
  have hi : ∀ e, ¬ rel e e := fun _ h => h
  have ht : ∀ e f g, rel e f → rel f g → rel e g := fun _ _ _ h _ => h
  have hc : ∀ e f, rel e f → (attr e).time < (attr f).time := fun _ _ h => h.elim
  let c := TaggedPresentation.contextOf code attr rel hi ht hc Finset.univ
  let selected : Finset E := Finset.univ.filter (fun e => e.2.2 = decide (0 ≤ r e.1.val))
  let X : Rich d := ⟨c, TaggedPresentation.selectionOf code attr rel hi ht hc
    Finset.univ selected (Finset.subset_univ _)⟩
  have transport (s : Finset E) :
      spatialCharge c (s.map (TaggedPresentation.eventEquiv code).toEmbedding) =
        ∑ e ∈ s, Finsupp.single e.1.val (if e.2.2 then (1 : Int) else -1) := by
    dsimp only [spatialCharge, contribution, c, TaggedPresentation.contextOf,
      TaggedPresentation.archiveOf]
    rw [Finset.sum_map]
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl
  refine ⟨X, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.univ_map_equiv_to_embedding (TaggedPresentation.eventEquiv code)
  · intro e; rfl
  · intro e f h; exact h
  · intro e
    exact ((TaggedPresentation.eventEquiv code).symm e).1.property
  · change charge (TaggedPresentation.contextOf code attr rel hi ht hc Finset.univ)
      (Finset.univ.map (TaggedPresentation.eventEquiv code).toEmbedding) = 0
    rw [TaggedPresentation.charge_map code attr rel hi ht hc Finset.univ Finset.univ]
    change (∑ e : E, if e.2.2 then (1 : Int) else -1) = 0
    rw [Fintype.sum_sigma]
    simp [Fintype.sum_prod_type]
  · change spatialCharge c (Finset.univ.map _) = 0
    rw [transport, Fintype.sum_sigma]
    simp [Fintype.sum_prod_type]
  · change spatialCharge c (selected.map _) = r
    rw [transport]
    simp only [selected, Finset.sum_filter]
    rw [Fintype.sum_sigma]
    simp_rw [Fintype.sum_prod_type]
    have fibre (y : r.support) :
        (∑ i : Fin (r y.val).natAbs, ∑ b : Bool,
          if b = decide (0 ≤ r y.val) then
            Finsupp.single y.val (if b then (1 : Int) else -1) else 0) =
          Finsupp.single y.val (r y.val) := by
      cases hn : r y.val with
      | ofNat n =>
        ext z
        simp [Finsupp.single_apply]
      | negSucc n =>
        ext z
        simp [Finsupp.single_apply]
        split_ifs <;> omega
    simp_rw [fibre]
    exact (Finset.sum_coe_sort r.support (fun y => Finsupp.single y (r y))).trans
      (Finsupp.sum_single r)

end
end D5.S3.ConceptDynamics.Spacetime.SignedProfileRealization
