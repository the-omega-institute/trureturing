/- GID: D5/S3/Combinatorics/CayleySumCodes/TotalCodeParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/TotalCodeParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite total perfect code has an induced perfect matching and even cardinality. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.TotalCodeParity

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

variable {G : Type*} [Group G]

/-- The open-neighbor condition restricts to a one-regular induced graph on
the code itself, so a finite total perfect code has even cardinality. This
applies to arbitrary code subsets, including subgroup codes. -/
theorem result [Finite G] (graph : SimpleGraph G) (C : Set G)
    (hc : IsTotalPerfectCode graph C) :
    (∀ v : C, Nat.card ((graph.induce C).neighborSet v) = 1) ∧ Even (Nat.card C) := by
  classical
  let : Fintype C := Fintype.ofFinite C
  have unique (v : C) : ∃! w : C, (graph.induce C).Adj v w := by
    obtain ⟨w, ⟨hw, he⟩, hu⟩ := hc v.1
    refine ⟨⟨w, hw⟩, he, ?_⟩
    intro z hz
    exact Subtype.ext (hu z.1 ⟨z.2, hz⟩)
  have degree (v : C) : (graph.induce C).degree v = 1 := by
    obtain ⟨w, hw, hu⟩ := unique v
    have hcard : Fintype.card ((graph.induce C).neighborSet v) = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨w, hw⟩, fun z => Subtype.ext (hu z.1 z.2)⟩
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard
  refine ⟨?_, ?_⟩
  · intro v
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] using degree v
  · have hand := (graph.induce C).even_card_odd_degree_vertices
    have one_odd : Odd (1 : ℕ) := by decide
    simpa only [degree, one_odd, Finset.filter_true, Finset.card_univ,
      Nat.card_eq_fintype_card] using hand

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.TotalCodeParity
