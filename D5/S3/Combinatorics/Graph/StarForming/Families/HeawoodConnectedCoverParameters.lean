/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Exact SF and the connected/disconnected beta dichotomy for Heawood double lifts. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodCertificates
import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodSixRepresentatives

/-! The six-type parameter transfer in HEAWOOD_DOUBLE_COVER_GAIN,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
open StarFormingDissociationRefutation HeawoodSwitching HeawoodLift
open D5.S3.Combinatorics.Graph.StarForming.Families

private theorem six_adjacency : ∀ k : Fin 6, ∀ x y : Fin 14 × F2,
    HeawoodCertificates.adjacency (HeawoodCertificates.sixTwists k) (pack x) (pack y) ↔
      (base.Adj x.1 y.1 ∧
        x.2 + y.2 = HeawoodSixRepresentatives.representative k (edgeIndex x.1 y.1)) := by
  decide +kernel

/-- The six supplier graphs are exactly the six binary voltage graphs. -/
def sixIso (k : Fin 6) : graph (HeawoodSixRepresentatives.representative k) ≃g
    HeawoodCertificates.sixGraph k where
  toEquiv := pack
  map_rel_iff' := by intro x y; exact six_adjacency k x y

/-- Connected binary Heawood lifts have beta fifteen or sixteen. -/
theorem connected_beta (s : Signing) (hs : (graph s).Preconnected) :
    15 ≤ beta (graph s) 2 ∧ beta (graph s) 2 ≤ 16 := by
  obtain ⟨k,⟨e⟩⟩ := HeawoodSixRepresentatives.exists_representative s hs
  have h := Isomorphism.parameters (e.trans (sixIso k))
  rw [h.1]
  exact HeawoodCertificates.six_beta_bounds k

/-- The complete two-sheet dichotomy uses actual connectedness and finite maxima. -/
theorem parameters (s : Signing) :
    SF (graph s) 2=16 ∧
    (beta (graph s) 2=14 ↔ ¬ (graph s).Preconnected) ∧
    ((graph s).Preconnected →
      (beta (graph s) 2=15 ∨ beta (graph s) 2=16) ∧ SF (graph s) 2-beta (graph s) 2≤1) := by
  classical
  refine ⟨sf_all s,⟨?_,disconnected_beta s⟩,?_⟩
  · intro hb hc
    have h := (connected_beta s hc).1
    omega
  · intro hc
    have hb := connected_beta s hc
    rw [sf_all]
    omega

end D5.S3.Combinatorics.Graph.StarForming.HeawoodCoverParameters
