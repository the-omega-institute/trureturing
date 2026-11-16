/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodCoverDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Density and gap bounds above the original S and J Heawood two-lifts. -/

import D5.S3.Combinatorics.Graph.StarForming.CoverDensity
import D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates

namespace D5.S3.Combinatorics.Graph.StarForming.CoverDensity
open StarFormingDissociationRefutation

/-- Every uniform cover above either original S or J two-lift has the stronger
four-sevenths density and one-forty-ninth gap bounds. No deck-group or switching
classification is assumed or claimed. -/
theorem scalar_cover_bound {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28)
    (cover : CoverPullback.NeighborhoodCover
      HeawoodCertificates.scalarGraph.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    4 * Fintype.card U ≤ 7 * beta H 2 ∧
      49 * (SF H 2 - beta H 2) ≤ Fintype.card U := by
  have hd := certificate_density HeawoodCertificates.scalarGraph H p cover k hk
    HeawoodCertificates.scalarSet HeawoodCertificates.scalar_selection.1
  have hg := cubic_certificate_gap HeawoodCertificates.scalarGraph H p cover k hk
    HeawoodCertificates.scalar_class.1 HeawoodCertificates.scalar_class.2
    HeawoodCertificates.scalarSet HeawoodCertificates.scalar_selection.1
  rw [HeawoodCertificates.scalar_selection.2] at hd hg
  norm_num at hd hg
  constructor <;> omega

theorem jordan_cover_bound {U : Type} [Fintype U] [DecidableEq U]
    (H : SimpleGraph U) [DecidableRel H.Adj] (p : U → Fin 28)
    (cover : CoverPullback.NeighborhoodCover
      HeawoodCertificates.jordanGraph.Adj H.Adj p) (k : ℕ)
    (hk : ∀ v, (Finset.univ.filter (fun w => p w = v)).card = k) :
    4 * Fintype.card U ≤ 7 * beta H 2 ∧
      49 * (SF H 2 - beta H 2) ≤ Fintype.card U := by
  have hd := certificate_density HeawoodCertificates.jordanGraph H p cover k hk
    HeawoodCertificates.jordanSet HeawoodCertificates.jordan_selection.1
  have hg := cubic_certificate_gap HeawoodCertificates.jordanGraph H p cover k hk
    HeawoodCertificates.jordan_class.1 HeawoodCertificates.jordan_class.2
    HeawoodCertificates.jordanSet HeawoodCertificates.jordan_selection.1
  rw [HeawoodCertificates.jordan_selection.2] at hd hg
  norm_num at hd hg
  constructor <;> omega

end D5.S3.Combinatorics.Graph.StarForming.CoverDensity
