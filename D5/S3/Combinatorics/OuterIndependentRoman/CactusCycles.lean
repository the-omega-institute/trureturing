/- GID: D5/S3/Combinatorics/OuterIndependentRoman/CactusCycles
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OuterIndependentRoman/CactusCycles
   mirror-E: none(waiver:fundamental-cycle-count)
   anchors: []
   utility: none
   digest: The existing fundamental-cycle family bounds the number of non-tree edges. -/

import D5.S3.Combinatorics.OuterIndependentRoman.CactusDefs
import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OuterIndependentRoman.CactusCycles

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fundamental cycles inject the edges outside a spanning tree into cycle edge sets. -/
theorem nonTreeEdges_le_cycles (G T : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel T.Adj] (hTG : T ≤ G) (hT : T.IsTree) :
    (G.edgeFinset \ T.edgeFinset).card ≤ (CactusDefs.cycleEdgeSets G).ncard := by
  classical
  let q := G.edgeFinset \ T.edgeFinset
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let : MeasurableSpace (ZMod 2) := ⊤
  have hreach : T.Reachable = G.Reachable := by
    funext u v
    exact propext ⟨fun h => h.mono hTG, fun _ => hT.connected.preconnected u v⟩
  have hall := D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace.finite_graph_cycle_space G
  obtain ⟨cycles, hcycles, _, hind, _⟩ :=
    hall.2.2 T hTG hT.isAcyclic hreach
  let D := {e : G.edgeSet // e.val ∉ T.edgeSet}
  let toD (e : Sym2 V) (he : e ∈ q) : D :=
    ⟨⟨e, mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1⟩,
      fun h => (Finset.mem_sdiff.mp he).2 (mem_edgeFinset.mpr h)⟩
  let f (e : Sym2 V) : Finset (Sym2 V) :=
    if he : e ∈ q then (cycles (toD e he)).2.edges.toFinset else ∅
  have hf : ∀ e ∈ q, f e ∈ CactusDefs.cycleEdgeSets G := by
    intro e he
    exact ⟨(cycles (toD e he)).1, (cycles (toD e he)).2,
      hcycles (toD e he), by simp [f, he]⟩
  have hinj : Set.InjOn f (q : Set (Sym2 V)) := by
    intro e he e' he' h
    change e ∈ q at he
    change e' ∈ q at he'
    have hself : e ∈ (cycles (toD e he)).2.edges := by
      have hd := hind (toD e he) (toD e he)
      by_contra hn
      simp [toD, hn] at hd
    have hmem : e ∈ (cycles (toD e' he')).2.edges := by
      have hefin : e ∈ f e := by simpa [f, he] using hself
      have hefin' : e ∈ f e' := h ▸ hefin
      simpa [f, he'] using hefin'
    have hd := hind (toD e' he') (toD e he)
    have hde : toD e he = toD e' he' := by
      by_contra hn
      simp [toD, hmem, hn] at hd
    exact congrArg (fun d : D => d.val.val) hde
  change q.card ≤ (CactusDefs.cycleEdgeSets G).ncard
  rw [← Set.ncard_coe_finset q]
  exact Set.ncard_le_ncard_of_injOn f hf hinj

#print axioms nonTreeEdges_le_cycles

end D5.S3.Combinatorics.OuterIndependentRoman.CactusCycles
