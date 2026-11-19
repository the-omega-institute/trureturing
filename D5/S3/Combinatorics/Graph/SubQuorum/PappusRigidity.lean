/- GID: D5/S3/Combinatorics/Graph/SubQuorum/PappusRigidity
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/PappusRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Symbolic support and coloring rigidity for Pappus. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives

/-! The pair-packing bound applies to arbitrary feasible supports and matchings.
Choosing representatives from an arbitrary ten-color sub-quorum coloring then
forces every color class to have one vertex and the support to be a dissociation set.
Source PR #28593, Sahbi revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

namespace D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
open StarFormingDissociationRefutation
open StarForming
open DoubleStarGrafting

/-- Every Pappus optimum has no matching representative, preserving the full
support-rigidity assertion beyond the numerical value ten. -/
theorem pappus_optimal_matching_empty (T : Finset (Fin 18)) (M : Finset (Fin 18 × Fin 18))
    (hf : Feasible pappusGraph T M) (hc : T.card + M.card = 10) : M = ∅ := by
  have hh := positive_excess_budget pappusGraph pappusColor pappusColor_valid
    pappus_class.2.2 3 9 (by decide) pappus_class.2.1 (paritySide_card 9) T M hf (by omega)
  norm_num at hh
  apply Finset.card_eq_zero.mp
  omega

/-- Every ten-color Pappus coloring has an actual ten-vertex dissociation support
and is injective on that support; this is a statement about every optimum. -/
theorem pappus_coloring_rigidity (c : Fin 18 → Option ℕ)
    (hc : IsSubQuorum pappusGraph c) (hp : (palette c Finset.univ).card = 10) :
    IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) ∧
    (coloredSupport c Finset.univ).card = 10 ∧
    Set.InjOn c (coloredSupport c Finset.univ) := by
  classical
  obtain ⟨T,M,hf,he,hclasses⟩ := coloring_representatives pappusGraph c hc
  have hm := pappus_optimal_matching_empty T M hf (he.trans hp)
  have hclass := hclasses hm
  have hi : IsKIndependent pappusGraph 2 (coloredSupport c Finset.univ) := by
    intro v hv
    have hvc := (Finset.mem_filter.mp hv).2
    have hsame : ((Finset.univ.filter (pappusGraph.Adj v)).filter
        (fun w => c w = c v)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro w hw he
      exact hclass v w hvc he (Finset.mem_filter.mp hw).2
    have hh := hc v hvc
    have hneigh : @Finset.filter (Fin 18) (pappusGraph.Adj v)
        (fun _ => Classical.propDecidable _) Finset.univ =
        Finset.univ.filter (pappusGraph.Adj v) := by ext w; simp
    have hs : ((Finset.univ.filter (pappusGraph.Adj v)).filter (fun w => c w ≠ none)) =
        (coloredSupport c Finset.univ).filter (pappusGraph.Adj v) := by
      ext w
      simp [coloredSupport,and_comm]
    rw [hneigh,hsame,hs] at hh
    simp only [Finset.card_empty] at hh
    omega
  have hu : (coloredSupport c Finset.univ).card ≤ beta pappusGraph 2 :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hi⟩)
  have hl : (palette c Finset.univ).card ≤ (coloredSupport c Finset.univ).card :=
    Finset.card_image_le
  rw [beta_pappus] at hu
  have hcard : (coloredSupport c Finset.univ).card = 10 := by omega
  refine ⟨hi,hcard,?_⟩
  apply Finset.card_image_iff.mp
  exact hp.trans hcard.symm

end D5.S3.Combinatorics.Graph.SubQuorum.C4FreeRepresentatives
