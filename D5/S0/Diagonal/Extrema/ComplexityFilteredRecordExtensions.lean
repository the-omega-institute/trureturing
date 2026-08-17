/- GID: D5/S0/Diagonal/Extrema/ComplexityFilteredRecordExtensions
   generality: G
   mirror-B: D5/B/S0/Diagonal/Extrema/ComplexityFilteredRecordExtensions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite complexity filters eventually contain every record extension. -/

import D5.S0.Diagonal.RecordExtensionCount

/-!
Every natural-valued complexity filter on a finite function space eventually contains every
record extension. The source's explicit upper bound for the threshold REMAINS OPEN and is not
discharged.
-/

universe u v

namespace D5.S0.Diagonal.Extrema.ComplexityFilteredRecordExtensions

open D5.S0.Diagonal.RecordExtensionCount

theorem restricted_extension_card_eventually_eq
    {D : Type u} {Y : Type v} [Fintype D] [Fintype Y]
    (complexity : (D -> Y) -> Nat) (record : Finset D) (prescribed : D -> Y) :
    ∃ Qstar : Nat, ∀ Q ≥ Qstar,
      Nat.card (RestrictedExtensions {f | complexity f ≤ Q} record prescribed) =
        Fintype.card Y ^ (Fintype.card D - record.card) := by
  classical
  refine ⟨Finset.univ.sup complexity, ?_⟩
  intro Q hQ
  have hcandidate : {f : D -> Y | complexity f ≤ Q} = Set.univ := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact (Finset.le_sup (Finset.mem_univ f)).trans hQ
  rw [hcandidate]
  simpa [RestrictedExtensions, RecordExtensions] using
    (record_extension_card record prescribed)

end D5.S0.Diagonal.Extrema.ComplexityFilteredRecordExtensions
