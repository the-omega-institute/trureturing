/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricActualHighProfiles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricActualHighProfiles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Transfer the side profiles and saturation inequalities to the graph actually induced by degree-three vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles
import Batteries.Tactic.OpenPrivate

/-! Actual induced high-graph degrees, side profiles and saturated neighbor sums.
The bridges below are finite bijections on actual vertices and neighbors. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles

open SimpleGraph GirthSliceCounting
open scoped BigOperators

attribute [local instance] Classical.propDecidable

open private High graph side graph_degree high_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
open private highDegree highTypeA highTypeB highProfile symmetric_high_profiles
  symmetric_high_profile_saturation from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighProfiles

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem side_degree_filter_card (G : SimpleGraph V) (L : Finset V) (k : ℕ) :
    ((side G L).filter fun x => (graph G).degree x = k).card =
      ((degreeThree G L).filter fun x => highDegree G x = k).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have hm := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm.1).2, x.property⟩
    · simpa only [graph_degree, highDegree] using hm.2
  · intro x _ y _ he
    exact Subtype.ext he
  · intro y hy
    have hm := Finset.mem_filter.mp hy
    have hy3 := Finset.mem_filter.mp hm.1
    refine ⟨⟨y, hy3.2⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨by simp [side, hy3.1], ?_⟩
    simpa only [graph_degree, highDegree] using hm.2

private theorem neighbor_degree_sum (G : SimpleGraph V) (x : High G) :
    (∑ y ∈ (graph G).neighborFinset x, (graph G).degree y) =
      ∑ y ∈ degreeThree G (G.neighborFinset x.val), highDegree G y := by
  apply Finset.sum_bij (fun y _ => y.val)
  · intro y hy
    have hxy : (graph G).Adj x y := ((graph G).mem_neighborFinset _ _).mp hy
    have hxy' : G.Adj x.val y.val := hxy
    exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxy', y.property⟩
  · intro y _ z _ he
    exact Subtype.ext he
  · intro y hy
    have hm := Finset.mem_filter.mp hy
    refine ⟨⟨y, hm.2⟩, ?_, rfl⟩
    apply ((graph G).mem_neighborFinset _ _).mpr
    exact (G.mem_neighborFinset _ _).mp hm.1
  · intro y _hy
    exact graph_degree G y

private def sideDegreeTuple (G : SimpleGraph V) (L : Finset V) : ℕ × ℕ × ℕ :=
  (((side G L).filter fun x => (graph G).degree x = 1).card,
    ((side G L).filter fun x => (graph G).degree x = 2).card,
    ((side G L).filter fun x => (graph G).degree x = 3).card)

private theorem side_degree_tuple (G : SimpleGraph V) (L : Finset V) :
    sideDegreeTuple G L =
      (((degreeThree G L).filter fun x => highDegree G x = 1).card,
        ((degreeThree G L).filter fun x => highDegree G x = 2).card,
        ((degreeThree G L).filter fun x => highDegree G x = 3).card) := by
  simp only [sideDegreeTuple, side_degree_filter_card]

private theorem side_typeB_iff (G : SimpleGraph V) (L : Finset V) :
    sideDegreeTuple G L = (2, 4, 1) ↔ highTypeB G (degreeThree G L) := by
  unfold highTypeB
  rw [side_degree_tuple]

private theorem degree_range_of_profile {G : SimpleGraph V} {L : Finset V}
    (hp : highProfile G (degreeThree G L)) {x : High G} (hx : x ∈ side G L) :
    (graph G).degree x = 1 ∨ (graph G).degree x = 2 ∨ (graph G).degree x = 3 := by
  have hx3 : x.val ∈ degreeThree G L :=
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2, x.property⟩
  have hr := hp.2.2 x.val hx3
  have hd : (graph G).degree x = highDegree G x.val := graph_degree G x
  omega

variable {G : SimpleGraph V} {L R : Finset V}

/-- Both actual side profiles are derived from the original symmetric-slice
conditions, and every vertex of the induced high graph has degree one to three. -/
private theorem actual_high_profiles
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4) :
    (∀ x, (graph G).degree x = 1 ∨ (graph G).degree x = 2 ∨ (graph G).degree x = 3) ∧
    (sideDegreeTuple G L = (1, 6, 0) ∨ sideDegreeTuple G L = (2, 4, 1)) ∧
    (sideDegreeTuple G R = (1, 6, 0) ∨ sideDegreeTuple G R = (2, 4, 1)) := by
  obtain ⟨_, _, hLp, hRp, _, _, _, _⟩ :=
    symmetric_high_profiles hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨_, hu, _⟩ := high_partition hpart hdeg
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx : x ∈ side G L ∪ side G R := by
      rw [hu]
      exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with hxL | hxR
    · exact degree_range_of_profile hLp hxL
    · exact degree_range_of_profile hRp hxR
  · simpa only [side_degree_tuple, highTypeA, highTypeB] using hLp.2.1
  · simpa only [side_degree_tuple, highTypeA, highTypeB] using hRp.2.1

/-- Opposite-side saturation is transported to every actual induced high vertex.
The B conditions are the original actual high-point profiles. -/
private theorem actual_high_saturation_of_original_typeB
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hL : L.card = 11) (hR : R.card = 11)
    (hL2 : (degreeTwo G L).card = 4) (hR2 : (degreeTwo G R).card = 4)
    (hLB : highTypeB G (degreeThree G L)) (hRB : highTypeB G (degreeThree G R)) :
    ∀ x, (∑ y ∈ (graph G).neighborFinset x, (graph G).degree y) =
      (graph G).degree x + 2 := by
  obtain ⟨hLs, hRs, _, _⟩ :=
    symmetric_high_profile_saturation hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨_, hu, _⟩ := high_partition hpart hdeg
  intro x
  have hx : x ∈ side G L ∪ side G R := by
    rw [hu]
    exact Finset.mem_univ x
  have hlocal :
      (∑ y ∈ degreeThree G (G.neighborFinset x.val), highDegree G y) =
        highDegree G x.val + 2 := by
    rcases Finset.mem_union.mp hx with hxL | hxR
    · exact hLs hRB x.val
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxL).2, x.property⟩)
    · exact hRs hLB x.val
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxR).2, x.property⟩)
  calc
    _ = ∑ y ∈ degreeThree G (G.neighborFinset x.val), highDegree G y :=
      neighbor_degree_sum G x
    _ = highDegree G x.val + 2 := hlocal
    _ = (graph G).degree x + 2 :=
      congrArg (fun n : ℕ => n + 2) (graph_degree G x).symm

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricActualHighProfiles
