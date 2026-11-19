/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Form the actual graph induced by degree-three vertices, preserving full-graph incidences and deriving its degrees, bipartition and girth. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal
import Batteries.Tactic.OpenPrivate

/-! The actual graph induced by degree-three vertices of a symmetric slice.
These adapters keep degree, side cardinality and girth attached to real edges. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph

open SimpleGraph GirthSliceCounting

attribute [local instance] Classical.propDecidable

open private symmetric_high_counts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyTwoLocal

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev High (G : SimpleGraph V) := {v : V // G.degree v = 3}

private def graph (G : SimpleGraph V) : SimpleGraph (High G) :=
  G.induce {v | G.degree v = 3}

private def side (G : SimpleGraph V) (L : Finset V) : Finset (High G) :=
  Finset.univ.filter fun x => x.val ∈ L

private theorem graph_degree (G : SimpleGraph V) (x : High G) :
    (graph G).degree x = (degreeThree G (G.neighborFinset x.val)).card := by
  have hmap := G.map_neighborFinset_induce (s := {v | G.degree v = 3}) x
  have hcard := congrArg Finset.card hmap
  have hf : G.neighborFinset x.val ∩ ({v | G.degree v = 3} : Set V).toFinset =
      degreeThree G (G.neighborFinset x.val) := by
    ext y
    simp [degreeThree]
  rw [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree, hf] at hcard
  exact hcard

private theorem side_card (G : SimpleGraph V) (L : Finset V) :
    (side G L).card = (degreeThree G L).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, x.property⟩
  · intro x _ y _ he
    exact Subtype.ext he
  · intro y hy
    have hm := Finset.mem_filter.mp hy
    exact ⟨⟨y, hm.2⟩, by simp [side, hm.1], rfl⟩

private theorem actual_partition
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) (v : V) :
    v ∈ L ∨ v ∈ R := by
  have hp : 0 < G.degree v := by rcases hdeg v with h | h <;> omega
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
  rcases hpart.mem_of_adj hvw with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

private theorem high_partition
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3) :
    Disjoint (side G L) (side G R) ∧
      side G L ∪ side G R = Finset.univ ∧
      (graph G).IsBipartiteWith (side G L : Set (High G))
        (side G R : Set (High G)) := by
  have hd : Disjoint (side G L) (side G R) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp hpart.disjoint
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  refine ⟨hd, ?_, ?_⟩
  · ext x
    have hv := actual_partition hpart hdeg x.val
    simp [side, hv]
  · refine ⟨by exact_mod_cast hd, ?_⟩
    intro x y hxy
    have hxy' : G.Adj x.val y.val := hxy
    rcases hpart.mem_of_adj hxy' with h | h
    · left
      simpa [side] using h
    · right
      simpa [side] using h

private theorem high_graph_girth {G : SimpleGraph V} (hg : (8 : ℕ∞) ≤ G.egirth) :
    (8 : ℕ∞) ≤ (graph G).egirth := by
  exact hg.trans (SimpleGraph.Embedding.induce {v | G.degree v = 3}).isContained.egirth_le

private theorem symmetric_high_graph
    {G : SimpleGraph V} {L R : Finset V}
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4) :
    (side G L).card = 7 ∧ (side G R).card = 7 ∧
      Fintype.card (High G) = 14 ∧
      (8 : ℕ∞) ≤ (graph G).egirth ∧
      (graph G).IsBipartiteWith (side G L : Set (High G))
        (side G R : Set (High G)) ∧
      ∀ x, (graph G).degree x =
        (degreeThree G (G.neighborFinset x.val)).card := by
  obtain ⟨hl, hr, _, _⟩ := symmetric_high_counts hpart hdeg hlow hL hR hL2 hR2
  have hls : (side G L).card = 7 := (side_card G L).trans hl
  have hrs : (side G R).card = 7 := (side_card G R).trans hr
  obtain ⟨hd, hu, hb⟩ := high_partition hpart hdeg
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd, hls, hrs, Finset.card_univ] at hc
  exact ⟨hls, hrs, hc.symm, high_graph_girth hg, hb, graph_degree G⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
