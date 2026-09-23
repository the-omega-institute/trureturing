/- GID: D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ColoringCompactnessBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finsubgraph]
   utility: none
   digest: Finite palettes satisfy coloring compactness, while the natural palette fails it. -/

import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ColoringCompactnessBoundary

open SimpleGraph

/-- A fixed finite palette admits a global coloring exactly when every finite induced
subgraph does. In contrast, every finite induced subgraph of the complete graph on
`Set Nat` has a coloring by `Nat`, while the whole graph has none. -/
theorem finite_palette_compactness_and_infinite_palette_failure
    {V : Type*} (G : SimpleGraph V) (k : Nat) :
    ((Nonempty (G.Coloring (Fin k)) ↔
        ∀ s : Set V, s.Finite → Nonempty ((G.induce s).Coloring (Fin k))) ∧
      (∀ s : Set (Set Nat), s.Finite →
        Nonempty (((completeGraph (Set Nat)).induce s).Coloring Nat)) ∧
      ¬ Nonempty ((completeGraph (Set Nat)).Coloring Nat)) := by
  constructor
  · constructor
    · rintro ⟨c⟩ s _
      exact ⟨c.comp (Embedding.induce (G := G) s).toHom⟩
    · intro h
      apply nonempty_hom_of_forall_finite_subgraph_hom
      intro G' hG'
      have c := Classical.choice (h G'.verts hG')
      rw [induce_eq_coe_induce_top] at c
      exact c.comp (Subgraph.inclusion G'.le_induce_top_verts)
  · constructor
    · intro s hs
      let _ : Finite s := hs.to_subtype
      obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
      refine ⟨Coloring.mk (fun x => (e x : Nat)) ?_⟩
      intro x y hxy hcolor
      have he : e x = e y := Fin.ext hcolor
      have hxy' : x = y := e.injective he
      subst y
      exact ((completeGraph (Set Nat)).induce s).loopless.irrefl x hxy
    · rintro ⟨c⟩
      apply Function.cantor_injective c
      intro x y hxy
      by_contra hne
      exact c.valid (by simpa using hne) hxy

#print axioms finite_palette_compactness_and_infinite_palette_failure

end D5.S3.Combinatorics.Graph.ColoringCompactnessBoundary
