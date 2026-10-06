/- GID: D5/S3/Combinatorics/Graph/CycleSpaceEulerRank
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CycleSpaceEulerRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The binary graph cycle space is the first Betti space with Euler rank m-n+c. -/

import D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.CycleSpaceEulerRank

open SimpleGraph
open D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace

/-- The mod-two first Betti rank of a finite simple graph, represented by its
cycle space.  The identification with simplicial H₁ is the standard
one-dimensional graph chain model; this definition keeps the carrier already
formalized by SimpleGraphCycleSpace. -/
def graphBettiOne {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Nat :=
  Module.finrank (ZMod 2) (simpleCycleSpace G)

/-- The Euler cycle rank |E| - |V| + c, written with natural subtraction
after the forest inequality. -/
def eulerCycleRank {V : Type*} (G : SimpleGraph V)
    [Fintype V] [Fintype G.edgeSet] [Fintype G.ConnectedComponent] : Nat :=
  Fintype.card G.edgeSet + Fintype.card G.ConnectedComponent - Fintype.card V

/-- The finite binary cycle space has the Euler rank m - n + c.
This is the first-homology rank formula for a graph over ZMod 2,
packaged from the existing simple-cycle/fundamental-cycle basis theorem. -/
theorem graphBettiOne_eq_eulerCycleRank
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [Fintype G.ConnectedComponent]
    [MeasurableSpace (ZMod 2)] [MeasurableSingletonClass (ZMod 2)] :
    graphBettiOne G = eulerCycleRank G := by
  have h := finite_graph_cycle_space G
  rcases h with ⟨_, _, _, _, hforest, hrest⟩
  obtain ⟨T, hTG, hacyc, hreach⟩ := hforest
  have hdata := hrest T hTG hacyc hreach
  obtain ⟨cycles, _, _, _, basis, _, _, _, _, hcard, _, _, hfinrank, _⟩ := hdata
  calc
    graphBettiOne G = Nat.card {e : G.edgeSet // e.val ∉ T.edgeSet} := by
      simpa [graphBettiOne] using hfinrank
    _ = eulerCycleRank G := by
      simpa [eulerCycleRank] using hcard

#print axioms graphBettiOne_eq_eulerCycleRank

end D5.S3.Combinatorics.Graph.CycleSpaceEulerRank
