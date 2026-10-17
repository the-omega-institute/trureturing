/- GID: D5/S3/Combinatorics/Graph/Products/EmptyLayer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Products/EmptyLayer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: A chromatic maximum-degree bound yields a maximal independent set omitting a Cartesian layer. -/

import D5.S3.Combinatorics.Graph.Products.CayleyIndependence
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Fintype.Powerset

open SimpleGraph Finset

namespace CayleySquare

variable {V : Type*} [Fintype V] [Nonempty V]

/-- A coloring by at most the maximum degree allows a maximal independent set to omit a row. -/
theorem exists_maximalIndepSet_empty_layer (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchi : G.chromaticNumber ≤ (G.maxDegree : ℕ∞)) :
    ∃ I : Finset (V × V), Maximal (G □ G).IsIndepSet (I : Set (V × V)) ∧
      I.card ≤ (Fintype.card V - 1) * G.indepNum := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  obtain ⟨c⟩ := (G.chromaticNumber_le_iff_colorable).mp hchi
  have hcard : G.maxDegree = Fintype.card (G.neighborSet v) :=
    hv.trans (G.card_neighborSet_eq_degree v).symm
  let e : Fin G.maxDegree ≃ G.neighborSet v :=
    (finCongr hcard).trans (Fintype.equivFin _).symm
  let f : V → V × V := fun y => (e (c y), y)
  let T := univ.image f
  have hT : (G □ G).IsIndepSet (T : Set (V × V)) := by
    intro p hp q hq hpq hadj
    obtain ⟨y, _, rfl⟩ := mem_image.mp hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hq
    rcases hadj with ⟨h, he⟩ | ⟨h, he⟩
    · have he' : y = z := he
      subst z
      exact h.ne rfl
    · apply c.valid h
      exact e.injective (Subtype.ext he)
  let F : Finset (Finset (V × V)) := univ.filter fun J => (G □ G).IsIndepSet (J : Set (V × V))
  obtain ⟨I, hTI, hI⟩ := F.exists_le_maximal (mem_filter.mpr ⟨mem_univ T, hT⟩)
  have hi : (G □ G).IsIndepSet (I : Set (V × V)) := (mem_filter.mp hI.1).2
  have hm : Maximal (G □ G).IsIndepSet (I : Set (V × V)) := by
    refine ⟨hi, ?_⟩
    intro U hU hIU
    have hIU' : I ⊆ U.toFinset := by simpa using hIU
    have hUi : U.toFinset ⊆ I := hI.2 (mem_filter.mpr ⟨mem_univ _, by simpa using hU⟩) hIU'
    simpa using hUi
  have hvI : ∀ p ∈ I, p.1 ≠ v := by
    intro p hp he
    have ht : f p.2 ∈ I := hTI (mem_image.mpr ⟨p.2, mem_univ _, rfl⟩)
    have ha : (G □ G).Adj p (f p.2) := by
      refine Or.inl ⟨?_, rfl⟩
      change G.Adj p.1 (e (c p.2)).val
      rw [he]
      exact (e (c p.2)).property
    exact hi hp ht ha.ne ha
  refine ⟨I, hm, ?_⟩
  have hb := card_le_layer_bound G G I (univ.erase v) hi (by
    intro p hp
    exact mem_erase.mpr ⟨hvI p hp, mem_univ _⟩)
  simpa using hb

end CayleySquare
