/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Supplied exact six-bit orthogonality catalogue and complete proof transfer. -/

import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BinaryOrthogonality

theorem catalogue_covers : dimensionSix.Covers := by native_decide

theorem catalogue_proper : dimensionSix.Proper := by native_decide

theorem fifteen_colorable : graph.Colorable 15 :=
  dimensionSix.colorable catalogue_covers catalogue_proper

def cliqueIndex (i : Fin 15) : Fin dimensionSix.count :=
  ⟨cliqueIndices[i.val]! % dimensionSix.count, Nat.mod_lt _ dimensionSix.positive⟩

instance (U : Finset Vector) : Decidable (IsSpace U) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem clique_valid : ∀ i : Fin 15,
    IsSpace (dimensionSix.space (cliqueIndex i)) ∧
    dimensionSix.space (cliqueIndex i) ≠ {0} := by native_decide

def cliqueVertex (i : Fin 15) : Vertex :=
  ⟨dimensionSix.space (cliqueIndex i), clique_valid i⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem clique_adjacent : ∀ i j : Fin 15, i ≠ j →
    graph.Adj (cliqueVertex i) (cliqueVertex j) := by native_decide

/-- The full graph on all nonzero binary subspaces in six coordinates. -/
theorem chromatic_number_six : graph.chromaticNumber = 15 := by
  apply le_antisymm fifteen_colorable.chromaticNumber_le
  exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (by simp) cliqueVertex
    (fun i j h => clique_adjacent i j h)

#print axioms Catalogue.complete
#print axioms Catalogue.colorable
#print axioms chromatic_number_six

end BinaryOrthogonality
