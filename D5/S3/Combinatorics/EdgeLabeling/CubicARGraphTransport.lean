/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphTransport
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Additive rigidity of edge labels is invariant under graph isomorphism. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphTransport

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs

/-- Pull back an AR-labeling along a graph isomorphism. -/
theorem ar_graph_of_iso {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] (q : G ≃g H)
    (hH : IsARGraph H) : IsARGraph G := by
  classical
  obtain ⟨f,hbij,hvertex⟩ := hH
  let t : Sym2 V → Sym2 W := Sym2.map q
  have hinj : Function.Injective t := Sym2.map.injective q.injective
  have ht : Set.BijOn t G.edgeSet H.edgeSet := by
    refine ⟨?_,hinj.injOn,?_⟩
    · intro x hx
      exact q.toHom.map_mem_edgeSet hx
    · intro x hx
      refine ⟨(q.mapEdgeSet.symm ⟨x,hx⟩).val,
        (q.mapEdgeSet.symm ⟨x,hx⟩).property,?_⟩
      exact congrArg Subtype.val (q.mapEdgeSet.apply_symm_apply ⟨x,hx⟩)
  have hinc (v : V) (x : Sym2 V) :
      t x ∈ H.incidenceFinset (q v) ↔ x ∈ G.incidenceFinset v := by
    cases x with
    | h a b =>
      simp only [t, Sym2.map_mk, SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mk'_mem_incidenceSet_iff, q.map_adj_iff, q.injective.eq_iff]
  refine ⟨f ∘ t,?_,?_⟩
  · rw [q.card_edgeFinset_eq]
    exact hbij.comp ht
  · intro v S hS T hT hsum
    apply Finset.image_injective hinj
    apply hvertex (q v)
    · simp only [Finset.mem_coe, Finset.mem_powerset] at hS ⊢
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hinc v y).mpr (hS hy)
    · simp only [Finset.mem_coe, Finset.mem_powerset] at hT ⊢
      intro x hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact (hinc v y).mpr (hT hy)
    · simpa only [Finset.sum_image (fun _ _ _ _ heq => hinj heq), Function.comp_apply]
        using hsum

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphTransport
