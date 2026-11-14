/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodAllDoubleCovers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual parameter dichotomy for every two-sheeted Heawood neighborhood cover. -/

import D5.S3.Combinatorics.Graph.StarForming.BinaryCoverRepresentation
import D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The full two-sheet theorem of HEAWOOD_DOUBLE_COVER_GAIN,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69. The input
is an arbitrary actual neighborhood cover with two-element fibers. Neither
an original sheet labeling nor a prechosen voltage representation is assumed. -/
namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodAllDoubleCovers
open StarFormingDissociationRefutation Classical

/-- Every actual finite double cover has SF sixteen and beta fourteen exactly
when disconnected; connected covers have beta fifteen or sixteen and gap at
most one. The four remaining type-specific exact beta questions stay separate. -/
theorem parameters {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 14)
    (cover : CoverPullback.NeighborhoodCover HeawoodLift.base.Adj H.Adj p)
    (fibers : ∀ v, Nat.card {u // p u=v}=2) :
    SF H 2=16 ∧ (beta H 2=14 ↔ ¬ H.Preconnected) ∧
    (H.Preconnected → (beta H 2=15 ∨ beta H 2=16) ∧ SF H 2-beta H 2≤1) := by
  classical
  obtain ⟨s,⟨e⟩⟩ := @BinaryCoverRepresentation.representation
    (Fin 14) HeawoodLift.base U (inferInstance : Fintype U) p H cover
    (by intro v; simpa only [← Nat.card_eq_fintype_card] using fibers v)
  let f := e.trans (HeawoodLift.voltageIso s)
  have he := Isomorphism.parameters f
  have hc := SimpleGraph.Iso.preconnected_iff f
  have hp := HeawoodCoverParameters.parameters (HeawoodLift.signingOfVoltage s)
  rw [← he.1,← he.2] at hp
  simpa only [← hc] using hp

end D5.S3.Combinatorics.Graph.StarForming.HeawoodAllDoubleCovers
