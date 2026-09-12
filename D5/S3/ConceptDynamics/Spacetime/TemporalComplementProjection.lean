/- GID: D5/S3/ConceptDynamics/Spacetime/TemporalComplementProjection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/TemporalComplementProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Temporal composition transports event complements componentwise and projects their signed charge by affine cancellation. -/

import D5.S3.ConceptDynamics.Spacetime.TemporalComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.TemporalComplementProjection

open D5.S0.History.Spacetime.ArchiveCarrier
open D5.S3.ConceptDynamics.Spacetime.ComplementCharge
open D5.S3.ConceptDynamics.Spacetime.TemporalComposition
open D5.S3.ConceptDynamics.Spacetime.TaggedPresentation
noncomputable section
open scoped Classical
open scoped BigOperators

variable {d : Nat}

/-- The complement of a temporally joined selection is the disjoint sum of the
component complements, transported through the canonical event equivalence. -/
theorem complement_selection_projection {c e : Context d} (h : Guard c.archive e.archive)
    (a : Selection c) (b : Selection e) :
    (complement (selection h a b)).val =
      ((c.current \ a.val).disjSum (e.current \ b.val)).map
        (equiv c.archive e.archive h).toEmbedding := by
  change ((c.current.disjSum e.current).map _ \ (a.val.disjSum b.val).map _) = _
  rw [Finset.map_disjSum, Finset.map_disjSum]
  ext z
  obtain ⟨x, rfl⟩ := (equiv c.archive e.archive h).surjective z
  cases x <;> simp [Finset.mem_map, Finset.mem_disjSum]

/-- Temporal composition and event complement commute after projecting to the
signed charge; no balance assumption is needed because the background terms
cancel componentwise. -/
theorem temporal_complement_projection {c e : Context d} (h : Guard c.archive e.archive)
    (a : Selection c) (b : Selection e) :
    readout (complement (selection h a b)) =
      readout (complement a) + readout (complement b) := by
  change charge (context c e h) (complement (selection h a b)).val = _
  rw [complement_selection_projection]
  exact charge_disjSum c e h (c.current \ a.val) (e.current \ b.val)

/- The strict temporal guard additionally gives a discrete one-step gap. -/
theorem temporal_complement_projection_spec {c e : Context d}
    (h : Guard c.archive e.archive) (a : Selection c) (b : Selection e)
    (x : c.archive.Event) (y : e.archive.Event) :
    readout (complement (selection h a b)) =
        readout (complement a) + readout (complement b) ∧
      (c.archive.attributes x).time + 1 ≤ (e.archive.attributes y).time := by
  refine ⟨temporal_complement_projection h a b, ?_⟩
  have hxy := h x y
  omega

#print axioms complement_selection_projection
#print axioms temporal_complement_projection
#print axioms temporal_complement_projection_spec

end
end D5.S3.ConceptDynamics.Spacetime.TemporalComplementProjection
