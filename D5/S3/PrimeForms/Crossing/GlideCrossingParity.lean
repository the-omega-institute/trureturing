/- GID: D5/S3/PrimeForms/Crossing/GlideCrossingParity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/GlideCrossingParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free glide involution pairs a finite crossing set evenly. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches for glide parity, even crossing counts, and fixed-point-free
     involutions found no equivalent D5 declaration.
   * Pinned-Mathlib searches found `SimpleGraph.Subgraph.IsPerfectMatching.even_card` in
     `Mathlib.Combinatorics.SimpleGraph.Matching`; it supplies the parity conclusion below.
   * Pinned Mathlib had no direct theorem taking only an involution and fixed-point-free
     hypotheses. Loogle queries for that type shape returned no matching declaration, and the
     GitHub code-search API required authentication.
-/

import Mathlib.Combinatorics.SimpleGraph.Matching

namespace D5.S3.PrimeForms.Crossing.GlideCrossingParity

/-- A fixed-point-free glide involution pairs every crossing with exactly one distinct crossing,
so a finite crossing set has even cardinality. -/
theorem glide_crossing_count_even {Crossing : Type*} [Fintype Crossing]
    (glide : Crossing -> Crossing) (hInvolutive : Function.Involutive glide)
    (hFixedPointFree : forall crossing, Ne (glide crossing) crossing) :
    Even (Fintype.card Crossing) := by
  let G : SimpleGraph Crossing := SimpleGraph.fromRel fun x y => glide x = y
  have hPerfect : (⊤ : G.Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro crossing
    refine ⟨glide crossing, ?_, ?_⟩
    · change Ne crossing (glide crossing) ∧
        (glide crossing = glide crossing ∨ glide (glide crossing) = crossing)
      exact ⟨(hFixedPointFree crossing).symm, Or.inl rfl⟩
    · intro other hAdjacent
      change Ne crossing other ∧ (glide crossing = other ∨ glide other = crossing) at hAdjacent
      rcases hAdjacent.2 with hForward | hBackward
      · exact hForward.symm
      · have hMapped := congrArg glide hBackward
        simpa only [hInvolutive other] using hMapped
  exact hPerfect.even_card

#print axioms glide_crossing_count_even

end D5.S3.PrimeForms.Crossing.GlideCrossingParity
