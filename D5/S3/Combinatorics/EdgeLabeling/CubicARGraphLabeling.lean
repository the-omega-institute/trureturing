/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLabeling
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphLabeling
   mirror-E: none(waiver:helper-for-open-problem-resolution)
   anchors: []
   utility: none
   digest: Finite edge equivalences give exact interval labelings of cubic graphs. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLabeling

open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphDefs

/-- Extend a bijection on the actual edges to every unordered vertex pair. -/
def edgeLabel {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (e : G.edgeSet ≃ Fin m)
    (s : Sym2 V) : ℕ :=
  if h : s ∈ G.edgeSet then (e ⟨s, h⟩).val + 1 else 0

/-- The labels of actual edges are precisely the interval from one to m. -/
private theorem edgeLabel_bijOn {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ} (e : G.edgeSet ≃ Fin m) :
    Set.BijOn (edgeLabel G e) G.edgeSet (Set.Icc 1 m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    simp only [edgeLabel, dif_pos hs, Set.mem_Icc]
    exact ⟨by omega, by have h := (e ⟨s, hs⟩).isLt; omega⟩
  · intro s hs t ht h
    simp only [edgeLabel, dif_pos hs, dif_pos ht] at h
    have heq : e ⟨s, hs⟩ = e ⟨t, ht⟩ := Fin.ext (by omega)
    exact congrArg Subtype.val (e.injective heq)
  · intro r hr
    have hlow := hr.1
    have hhigh := hr.2
    let i : Fin m := ⟨r - 1, by omega⟩
    let s := e.symm i
    refine ⟨s.val, s.property, ?_⟩
    simp only [edgeLabel, dif_pos s.property]
    change (e (e.symm i)).val + 1 = r
    rw [e.apply_symm_apply]
    dsimp [i]
    omega

/-- Avoiding additive triples under an edge equivalence proves additive rigidity. -/
theorem arGraph_of_edge_equiv {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet ≃ Fin G.edgeFinset.card)
    (hdegree : ∀ v, G.degree v = 3)
    (hno : ∀ v, ∀ a ∈ G.incidenceFinset v, ∀ b ∈ G.incidenceFinset v,
      ∀ c ∈ G.incidenceFinset v, a ≠ b → a ≠ c → b ≠ c →
        edgeLabel G e a + edgeLabel G e b ≠ edgeLabel G e c) :
    IsARGraph G := by
  have hbij := edgeLabel_bijOn G e
  refine ⟨edgeLabel G e, hbij, fun v => ?_⟩
  apply ar_vertex_of_no_additive_relation G (edgeLabel G e) v (hdegree v)
  · intro a ha
    have hedge : a ∈ G.edgeSet :=
      G.incidenceSet_subset v ((G.mem_incidenceFinset v a).mp ha)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (hbij.mapsTo hedge).1
  · exact hbij.injOn.mono (by simpa using G.incidenceSet_subset v)
  · exact hno v

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphLabeling
