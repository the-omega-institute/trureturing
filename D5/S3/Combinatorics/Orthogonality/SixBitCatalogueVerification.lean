/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.catalogue_proper
   digest: Supplied exact six-bit orthogonality catalogue and complete proof transfer. -/

import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BinaryOrthogonality

/- The supplied Lean 4.33.0 source used native_decide for the following
four obligations. Its recorded provenance includes the four generated
catalogue_covers/catalogue_proper/clique_valid/clique_adjacent native axioms.
That historical evidence is retained in the scientific handoff. Current
admission instead requires ordinary kernel reduction of these same exact
predicates and unchanged tables; no native-evaluation axiom is added here.
These are pending proofs until the current scoped build actually succeeds. -/
theorem catalogue_covers : dimensionSix.Covers := by decide +kernel

theorem catalogue_proper : dimensionSix.Proper := by decide +kernel

theorem fifteen_colorable : graph.Colorable 15 :=
  dimensionSix.colorable catalogue_covers catalogue_proper

def cliqueIndex (i : Fin 15) : Fin dimensionSix.count :=
  ⟨cliqueIndices[i.val]! % dimensionSix.count, Nat.mod_lt _ dimensionSix.positive⟩

instance (U : Finset Vector) : Decidable (IsSpace U) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem clique_valid : ∀ i : Fin 15,
    IsSpace (dimensionSix.space (cliqueIndex i)) ∧
    dimensionSix.space (cliqueIndex i) ≠ {0} := by decide +kernel

def cliqueVertex (i : Fin 15) : Vertex :=
  ⟨dimensionSix.space (cliqueIndex i), clique_valid i⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem clique_adjacent : ∀ i j : Fin 15, i ≠ j →
    graph.Adj (cliqueVertex i) (cliqueVertex j) := by decide +kernel

/-- The full graph on all nonzero binary subspaces in six coordinates. -/
theorem chromatic_number_six : graph.chromaticNumber = 15 := by
  apply le_antisymm fifteen_colorable.chromaticNumber_le
  exact SimpleGraph.le_chromaticNumber_of_pairwise_adj (by simp) cliqueVertex
    (fun i j h => clique_adjacent i j h)

#print axioms Catalogue.complete
#print axioms Catalogue.colorable
#print axioms chromatic_number_six

end BinaryOrthogonality
